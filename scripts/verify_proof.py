#!/usr/bin/env python3
"""Trusted Lean 4 proof verification, lockfile integrity, and catalog harness.

Two-gate verification for every submitted solution `lean/InfoTheory/Solutions/<Module>.lean`:
  1. `lake build InfoTheory.Solutions.<Module>`
  2. `lake env leanchecker InfoTheory.Solutions.<Module>`
     Replays the compiled `.olean` through the Lean 4 kernel, catching
     `debug.skipKernelTC` / `addDecl` forgeries.
  3. `lake env lean --run ../scripts/CheckSolution.lean InfoTheory.Problems.<Module> InfoTheory.Solutions.<Module>`
     Loads the `.olean` environment directly with `trustLevel := 0` (no user syntax
     or custom elaborators run, preventing `#print axioms` spoofing), checks syntactic
     type equality with `Statement` or `¬ Statement`, checks module provenance, and
     walks the full transitive constant closure (including theorem bodies) to ensure
     only `{propext, Classical.choice, Quot.sound}` are used.

Statement freezing:
  `lean/STATEMENT_LOCK.json` records SHA-256 hashes of all Core modules, Problem
  statement modules, toolchain/lakefile config, and `scripts/CheckSolution.lean`.
  `--check-lock` verifies none of the frozen files have been altered.

Usage:
  python3 scripts/verify_proof.py --check-catalog
  python3 scripts/verify_proof.py --check-lock
  python3 scripts/verify_proof.py --update-lock
  python3 scripts/verify_proof.py --verify <problem-id>
  python3 scripts/verify_proof.py --verify-all
  python3 scripts/verify_proof.py --self-test
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBLEMS_DIR = ROOT / "problems"
LEAN_DIR = ROOT / "lean"
LEAN_CORE_DIR = LEAN_DIR / "InfoTheory" / "Core"
LEAN_PROBLEMS_DIR = LEAN_DIR / "InfoTheory" / "Problems"
LEAN_SOLUTIONS_DIR = LEAN_DIR / "InfoTheory" / "Solutions"
CHECK_SCRIPT = ROOT / "scripts" / "CheckSolution.lean"
LOCK_FILE = LEAN_DIR / "STATEMENT_LOCK.json"


def env_with_elan():
    env = os.environ.copy()
    elan_bin = str(Path.home() / ".elan" / "bin")
    if elan_bin not in env.get("PATH", "").split(os.pathsep):
        env["PATH"] = elan_bin + os.pathsep + env.get("PATH", "")
    return env


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def locked_files() -> list[Path]:
    files = [
        LEAN_DIR / "lean-toolchain",
        LEAN_DIR / "lakefile.toml",
        LEAN_DIR / "InfoTheory.lean",
        LEAN_DIR / "InfoTheory" / "Core.lean",
        LEAN_DIR / "InfoTheory" / "Problems.lean",
        CHECK_SCRIPT,
    ]
    if LEAN_CORE_DIR.is_dir():
        files.extend(sorted(LEAN_CORE_DIR.glob("*.lean")))
    if LEAN_PROBLEMS_DIR.is_dir():
        files.extend(sorted(LEAN_PROBLEMS_DIR.glob("*.lean")))
    return [f for f in files if f.is_file()]


def compute_lock_map() -> dict[str, str]:
    return {str(f.relative_to(ROOT)): sha256_file(f) for f in locked_files()}


def update_lock() -> int:
    data = {
        "schema": 1,
        "description": "SHA-256 lockfile freezing Core definitions, Problem statements, and checker.",
        "files": compute_lock_map(),
    }
    LOCK_FILE.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Updated {LOCK_FILE.relative_to(ROOT)} with {len(data['files'])} locked files.")
    return 0


def check_lock() -> int:
    if not LOCK_FILE.is_file():
        print(f"ERROR: missing lockfile {LOCK_FILE.relative_to(ROOT)}; run --update-lock", file=sys.stderr)
        return 1
    expected = json.loads(LOCK_FILE.read_text(encoding="utf-8")).get("files", {})
    actual = compute_lock_map()
    diffs = []
    for k in sorted(set(expected) | set(actual)):
        if k not in actual:
            diffs.append(f"  MISSING:  {k}")
        elif k not in expected:
            diffs.append(f"  UNLOCKED: {k}")
        elif expected[k] != actual[k]:
            diffs.append(f"  MODIFIED: {k}")
    if diffs:
        print("STATEMENT LOCK CHECK FAILED (frozen files changed):", file=sys.stderr)
        print("\n".join(diffs), file=sys.stderr)
        return 1
    print(f"STATEMENT LOCK CHECK PASSED: {len(actual)} frozen files match SHA-256 hashes.")
    return 0


def parse_frontmatter(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        raise ValueError(f"{path}: missing frontmatter")
    _, fm, _ = text.split("---", 2)
    meta = {}
    for line in fm.strip().splitlines():
        if not line.strip() or line.strip().startswith("#"):
            continue
        key, _, val = line.partition(":")
        val = val.strip()
        if val.startswith("[") and val.endswith("]"):
            val = [v.strip() for v in val[1:-1].split(",") if v.strip()]
        meta[key.strip()] = val
    return meta


def load_catalog():
    catalog = {}
    for md in sorted(PROBLEMS_DIR.glob("*.md")):
        meta = parse_frontmatter(md)
        pid = meta["id"]
        if pid != md.stem:
            raise ValueError(f"{md}: id={pid!r} != stem={md.stem!r}")
        catalog[pid] = (md, meta)
    return catalog


def strip_lean_comments(text: str) -> str:
    """Remove Lean block comments `/- ... -/` (nested) and line comments `-- ...`."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text[i : i + 2] == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i : i + 2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and text[i : i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            if text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def check_lean_problem_file(lean_path: Path, module_name: str, problem_id: str) -> list[str]:
    errors = []
    if not lean_path.is_file():
        return [f"Missing Lean file: {lean_path}"]
    raw = lean_path.read_text(encoding="utf-8")
    code = strip_lean_comments(raw)
    if f"namespace {module_name}" not in code:
        errors.append(f"{lean_path}: missing `namespace {module_name}`")
    if not re.search(r"\bdef\s+Statement\s*:\s*Prop\b", code):
        errors.append(f"{lean_path}: missing `def Statement : Prop`")
    if f'id := "{problem_id}"' not in code:
        errors.append(f"{lean_path}: missing matching `id := \"{problem_id}\"`")
    for lineno, line in enumerate(code.splitlines(), 1):
        # Catch `axiom` even after attributes like `@[attr]` or modifiers
        if re.search(r"(^|\s)(\@\[[^\]]*\]\s*)*(private\s+|protected\s+|noncomputable\s+)*axiom\b", line):
            errors.append(f"{lean_path}:{lineno}: custom `axiom` is forbidden in problem statements")
        if re.search(r"\bsorry\b", line):
            errors.append(f"{lean_path}:{lineno}: `sorry` is forbidden in problem statement files")
        if "debug.skipKernelTC" in line:
            errors.append(f"{lean_path}:{lineno}: `debug.skipKernelTC` is forbidden")
    return errors


def check_catalog() -> int:
    catalog = load_catalog()
    errors = []
    seen_lean_files = set()
    open_count = 0

    for pid, (md, meta) in catalog.items():
        if meta.get("status") in ("open", "partially-solved"):
            open_count += 1
        lean_mod = meta.get("lean_module")
        lean_file = meta.get("lean_file")
        if not lean_mod or not lean_file:
            errors.append(f"{md.name}: missing lean_module or lean_file frontmatter")
            continue
        lp = ROOT / lean_file
        seen_lean_files.add(lp.resolve())
        errors.extend(check_lean_problem_file(lp, lean_mod, pid))

    if LEAN_PROBLEMS_DIR.is_dir():
        for lp in sorted(LEAN_PROBLEMS_DIR.glob("*.lean")):
            if lp.resolve() not in seen_lean_files:
                errors.append(f"Orphan Lean problem file not referenced by any problems/*.md: {lp.name}")

    # Also check Core files for sorry/axiom
    if LEAN_CORE_DIR.is_dir():
        for cf in sorted(LEAN_CORE_DIR.glob("*.lean")):
            code = strip_lean_comments(cf.read_text(encoding="utf-8"))
            for lineno, line in enumerate(code.splitlines(), 1):
                if re.search(r"(^|\s)(\@\[[^\]]*\]\s*)*(private\s+|protected\s+|noncomputable\s+)*axiom\b", line):
                    errors.append(f"{cf}:{lineno}: custom `axiom` is forbidden in Core")
                if re.search(r"\bsorry\b", line):
                    errors.append(f"{cf}:{lineno}: `sorry` is forbidden in Core")

    aggregator = LEAN_DIR / "InfoTheory" / "Problems.lean"
    if aggregator.is_file():
        agg_text = aggregator.read_text(encoding="utf-8")
        for pid, (_, meta) in catalog.items():
            lean_mod = meta.get("lean_module", "")
            if lean_mod and f"import {lean_mod}" not in agg_text:
                errors.append(f"InfoTheory/Problems.lean missing `import {lean_mod}`")
    else:
        errors.append("Missing lean/InfoTheory/Problems.lean aggregator module")

    if errors:
        print(f"CATALOG CHECK FAILED ({len(errors)} errors):", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print(
        f"CATALOG CHECK PASSED: {len(catalog)} total problems "
        f"({open_count} open/partially-solved), all Lean Core & Problem statements clean."
    )
    return 0


def run_two_gate_check(prob_mod: str, sol_mod: str, cwd: Path = LEAN_DIR, timeout: int = 900) -> tuple[bool, str]:
    """Run build + leanchecker + CheckSolution.lean. Returns (ok, message)."""
    env = env_with_elan()

    # Gate 1: build both modules
    r_build = subprocess.run(
        ["lake", "build", prob_mod, sol_mod],
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if r_build.returncode != 0:
        return False, f"BUILD FAILED:\n{r_build.stdout}\n{r_build.stderr}"

    # Gate 2: kernel replay via leanchecker (catches debug.skipKernelTC / addDecl forgeries)
    r_lc = subprocess.run(
        ["lake", "env", "leanchecker", sol_mod],
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if r_lc.returncode != 0:
        return False, f"LEANCHECKER REJECTED {sol_mod}:\n{r_lc.stdout}\n{r_lc.stderr}"

    # Gate 3: direct `.olean` environment inspection with trustLevel=0 (catches sorryAx,
    # custom axioms, #print axioms spoofing, wrong type, wrong module, non-thm decls)
    r_cs = subprocess.run(
        ["lake", "env", "lean", "--run", str(CHECK_SCRIPT), prob_mod, sol_mod],
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if r_cs.returncode != 0:
        return False, f"CHECKSOLUTION REJECTED {sol_mod}:\n{r_cs.stdout}\n{r_cs.stderr}"

    return True, r_cs.stdout.strip()


def verify_problem(problem_id: str) -> int:
    catalog = load_catalog()
    if problem_id not in catalog:
        print(f"ERROR: unknown problem id {problem_id!r}", file=sys.stderr)
        return 1
    _, meta = catalog[problem_id]
    prob_mod = meta["lean_module"]
    short_name = prob_mod.split(".")[-1]
    sol_mod = f"InfoTheory.Solutions.{short_name}"
    sol_file = LEAN_SOLUTIONS_DIR / f"{short_name}.lean"

    if not sol_file.is_file():
        print(f"NO SOLUTION FILE: expected {sol_file.relative_to(ROOT)}")
        return 2

    ok, msg = run_two_gate_check(prob_mod, sol_mod)
    if not ok:
        print(f"VERIFICATION FAILED for {problem_id}:\n{msg}", file=sys.stderr)
        return 1

    print(f"VERIFIED {problem_id}: {msg} (leanchecker + CheckSolution passed)")
    return 0


def verify_all() -> int:
    catalog = load_catalog()
    if not LEAN_SOLUTIONS_DIR.is_dir():
        print("No solutions directory yet; 0 solutions verified.")
        return 0
    found = 0
    failures = 0
    for pid, (_, meta) in catalog.items():
        short_name = meta["lean_module"].split(".")[-1]
        if (LEAN_SOLUTIONS_DIR / f"{short_name}.lean").is_file():
            found += 1
            rc = verify_problem(pid)
            if rc != 0:
                failures += 1
    print(f"Verified {found - failures}/{found} submitted Lean solutions.")
    return 1 if failures else 0


def self_test() -> int:
    """Adversarial self-test in an isolated temp Lean project (never writes into `lean/`).

    Verifies the full attack matrix against Lean v4.36.0:
      1. Honest proof of `Statement`           -> ACCEPTED by leanchecker & CheckSolution
      2. Honest disproof of `¬ Statement`      -> ACCEPTED by leanchecker & CheckSolution
      3. `debug.skipKernelTC` forgery of False -> REJECTED by leanchecker
      4. `sorry` + `#print axioms` spoof       -> REJECTED by CheckSolution (sorryAx)
      5. Proof of a different statement        -> REJECTED by CheckSolution
      6. Custom `@[simp] axiom`                -> REJECTED by CheckSolution
    """
    print("Running adversarial two-gate verifier self-test in isolated temp project...")
    toolchain = (LEAN_DIR / "lean-toolchain").read_text(encoding="utf-8")

    with tempfile.TemporaryDirectory(prefix="infotheory_selftest_") as tmp:
        td = Path(tmp)
        (td / "lean-toolchain").write_text(toolchain, encoding="utf-8")
        (td / "lakefile.toml").write_text(
            'name = "SelfTest"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "SelfTest"\n',
            encoding="utf-8",
        )
        (td / "SelfTest").mkdir()
        (td / "SelfTest" / "ProbTrue.lean").write_text(
            "namespace SelfTest.ProbTrue\ndef Statement : Prop := ∀ n : Nat, n + 0 = n\nend SelfTest.ProbTrue\n",
            encoding="utf-8",
        )
        (td / "SelfTest" / "ProbFalse.lean").write_text(
            "namespace SelfTest.ProbFalse\ndef Statement : Prop := False\nend SelfTest.ProbFalse\n",
            encoding="utf-8",
        )
        # 1. Honest proof
        (td / "SelfTest" / "SolHonest.lean").write_text(
            "import SelfTest.ProbTrue\nnamespace SelfTest.SolHonest\n"
            "theorem proof : SelfTest.ProbTrue.Statement := fun n => Nat.add_zero n\n"
            "end SelfTest.SolHonest\n",
            encoding="utf-8",
        )
        # 2. Honest disproof
        (td / "SelfTest" / "SolDisproof.lean").write_text(
            "import SelfTest.ProbFalse\nnamespace SelfTest.SolDisproof\n"
            "theorem disproof : ¬ SelfTest.ProbFalse.Statement := fun h => h\n"
            "end SelfTest.SolDisproof\n",
            encoding="utf-8",
        )
        # 3. Kernel-bypass forgery of False using debug.skipKernelTC
        (td / "SelfTest" / "SolForgery.lean").write_text(
            "import Lean\nimport SelfTest.ProbFalse\nopen Lean\n"
            "namespace SelfTest.SolForgery\n"
            "def badDecl : Declaration := .thmDecl {\n"
            "  name := `SelfTest.SolForgery.proof, levelParams := [],\n"
            "  type := mkConst ``SelfTest.ProbFalse.Statement,\n"
            "  value := mkConst ``True.intro }\n"
            "set_option debug.skipKernelTC true in\n"
            "run_cmd Elab.Command.liftCoreM (addDecl badDecl)\n"
            "end SelfTest.SolForgery\n",
            encoding="utf-8",
        )
        # 4. Sorry + `#print axioms` elaborator spoof
        (td / "SelfTest" / "SolSpoof.lean").write_text(
            "import Lean\nimport SelfTest.ProbFalse\nopen Lean Elab Command\n"
            "elab (priority := high) \"#print \" \"axioms \" id:ident : command =>\n"
            "  logInfo m!\"'{id.getId}' does not depend on any axioms\"\n"
            "namespace SelfTest.SolSpoof\n"
            "theorem proof : SelfTest.ProbFalse.Statement := by sorry\n"
            "end SelfTest.SolSpoof\n",
            encoding="utf-8",
        )
        # 5. Wrong statement
        (td / "SelfTest" / "SolWrong.lean").write_text(
            "import SelfTest.ProbTrue\nnamespace SelfTest.SolWrong\n"
            "theorem proof : True := trivial\n"
            "end SelfTest.SolWrong\n",
            encoding="utf-8",
        )
        # 6. Custom axiom
        (td / "SelfTest" / "SolAxiom.lean").write_text(
            "import SelfTest.ProbFalse\nnamespace SelfTest.SolAxiom\n"
            "@[simp] axiom magic : False\n"
            "theorem proof : SelfTest.ProbFalse.Statement := magic\n"
            "end SelfTest.SolAxiom\n",
            encoding="utf-8",
        )

        cases = [
            ("honest proof", "SelfTest.ProbTrue", "SelfTest.SolHonest", True, "OK proof"),
            ("honest disproof", "SelfTest.ProbFalse", "SelfTest.SolDisproof", True, "OK disproof"),
            ("skipKernelTC forgery", "SelfTest.ProbFalse", "SelfTest.SolForgery", False, "LEANCHECKER REJECTED"),
            ("sorry + #print spoof", "SelfTest.ProbFalse", "SelfTest.SolSpoof", False, "sorryAx"),
            ("wrong statement", "SelfTest.ProbTrue", "SelfTest.SolWrong", False, "type mismatch"),
            ("custom @[simp] axiom", "SelfTest.ProbFalse", "SelfTest.SolAxiom", False, "SelfTest.SolAxiom.magic"),
        ]

        for label, pmod, smod, expect_ok, expect_substr in cases:
            ok, msg = run_two_gate_check(pmod, smod, cwd=td, timeout=180)
            if ok != expect_ok or expect_substr not in msg:
                print(
                    f"SELF-TEST FAILED on '{label}': expected ok={expect_ok} with {expect_substr!r}, "
                    f"got ok={ok}:\n{msg}",
                    file=sys.stderr,
                )
                return 1
            verdict = "ACCEPTED" if ok else "REJECTED"
            print(f"  [PASS] {label:24s} -> {verdict} ({expect_substr})")

    print("ADVERSARIAL SELF-TEST PASSED (all 6 cases verified against Lean 4 kernel).")
    return 0


def main():
    parser = argparse.ArgumentParser(description="Verify Lean 4 problem statements, lockfile, and proofs.")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check-catalog", action="store_true", help="Check all problems/*.md against lean/InfoTheory/Problems/*.lean")
    group.add_argument("--check-lock", action="store_true", help="Verify SHA-256 lockfile of frozen Core & Problem statements")
    group.add_argument("--update-lock", action="store_true", help="Regenerate lean/STATEMENT_LOCK.json")
    group.add_argument("--verify", metavar="PROBLEM_ID", help="Run two-gate Lean verification for PROBLEM_ID")
    group.add_argument("--verify-all", action="store_true", help="Run two-gate Lean verification on all submitted solutions")
    group.add_argument("--self-test", action="store_true", help="Run adversarial 6-case kernel verification self-test")
    args = parser.parse_args()

    if args.check_catalog:
        sys.exit(check_catalog())
    elif args.check_lock:
        sys.exit(check_lock())
    elif args.update_lock:
        sys.exit(update_lock())
    elif args.verify:
        sys.exit(verify_problem(args.verify))
    elif args.verify_all:
        sys.exit(verify_all())
    elif args.self_test:
        sys.exit(self_test())


if __name__ == "__main__":
    main()
