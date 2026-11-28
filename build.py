#!/usr/bin/env python3
"""Dependency-free static site generator:
  problems/ + lean/ + attempts/ + solved_catalog.py -> site/.

Generates BOTH sister catalogs under one site:
  - Open Problems in Information Theory (site/index.html, site/problems/<id>.html)
  - Solved Problems in Information Theory: Lean Proofs (site/solved/index.html, site/solved/<id>.html)
with automatic bidirectional links between open problems, classical Lean proofs, and
machine-checked problem certificates in lean/InfoTheory/Known/Certificates/.

Python 3 stdlib only. Markdown subset: #-#### headings, paragraphs, -/* and
numbered lists, > blockquotes, ``` fenced code, | tables, **bold**, *italic*,
`code`, [text](url), horizontal rules. $...$ / $$...$$ are passed through
untouched for MathJax.
"""
import html
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

from solved_catalog import SOLVED_CATEGORY_LABELS, SOLVED_THEOREMS

ROOT = Path(__file__).parent
SITE = ROOT / "site"
LEAN_SOLUTIONS_DIR = ROOT / "lean" / "InfoTheory" / "Solutions"
LEAN_CERTS_DIR = ROOT / "lean" / "InfoTheory" / "Known" / "Certificates"


def _resolve_git_ref():
    try:
        sha = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, stderr=subprocess.DEVNULL
        ).decode("utf-8").strip()
        if re.fullmatch(r"[0-9a-f]{7,40}", sha):
            return sha
    except Exception:
        pass
    env_sha = os.environ.get("GITHUB_SHA", "").strip()
    if re.fullmatch(r"[0-9a-f]{7,40}", env_sha):
        return env_sha
    return "main"


GITHUB_REF = _resolve_git_ref()
GITHUB_BLOB = f"https://github.com/gokhanmergen/information-theory-problems/blob/{GITHUB_REF}"

STATUS_LABELS = {
    "open": "open",
    "partially-solved": "partially solved",
    "solved": "solved",
}

FORMAL_STATUS_META = {
    "statement-false": (
        "statement false",
        "The frozen Lean 4 statement is known to be false as formalized (catalog modeling error pending statement fix); the underlying open mathematical problem remains open.",
    ),
    "disproved": (
        "disproved (formal)",
        "The frozen Lean 4 statement has been formally disproved (`¬ Statement` verified in Lean 4), while the broader underlying open problem may remain open.",
    ),
    "claimed-resolved": (
        "claimed resolved",
        "A recent preprint claims to resolve this problem, but the proof is not yet independently verified or peer-reviewed.",
    ),
    "expected-false": (
        "expected false",
        "The frozen Lean 4 statement is open, though experts/heuristics expect the answer to be negative.",
    ),
}

CATEGORY_LABELS = {
    "entropy-inequalities": "Entropy Inequalities & Geometry",
    "channel-capacity": "Channel Capacity & Synchronization",
    "network-info-theory": "Network Information Theory",
    "source-coding": "Source Coding & Compression",
    "zero-error": "Zero-Error & Graph Capacity",
    "coding-theory": "Coding Theory & Bounds",
    "network-coding": "Network Coding & Storage",
    "quantum-info": "Quantum Information Theory",
    "security-privacy": "Security, Privacy & Secrecy",
    "statistical-info-theory": "Statistical Info Theory & Testing",
}


def fail(msg):
    sys.exit(f"build error: {msg}")


def parse_frontmatter(path):
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        fail(f"{path}: missing frontmatter")
    try:
        _, fm, body = text.split("---", 2)
    except ValueError:
        fail(f"{path}: unterminated frontmatter")
    meta = {}
    for line in fm.strip().splitlines():
        if not line.strip() or line.strip().startswith("#"):
            continue
        if ":" not in line:
            fail(f"{path}: bad frontmatter line: {line!r}")
        key, _, val = line.partition(":")
        val = val.strip()
        if val.startswith("[") and val.endswith("]"):
            val = [v.strip() for v in val[1:-1].split(",") if v.strip()]
        meta[key.strip()] = val
    return meta, body.strip()


# ---------------------------------------------------------------- markdown

def _protect(body, store):
    def stash(m):
        store.append(m.group(0))
        return f"\x00{len(store) - 1}\x00"

    body = re.sub(r"```.*?```", stash, body, flags=re.S)      # fenced code
    body = re.sub(r"\$\$.*?\$\$", stash, body, flags=re.S)    # display math
    body = re.sub(r"(?<!\$)\$(?!\$).+?(?<!\$)\$(?!\$)", stash, body)  # inline math
    body = re.sub(r"`[^`\n]+`", stash, body)                  # inline code
    return body


def _restore(text, store):
    def unstash(m):
        raw = store[int(m.group(1))]
        if raw.startswith("```"):
            code = raw.strip("`\n")
            code = code.split("\n", 1)[1] if "\n" in code else ""
            return f"<pre><code>{html.escape(code)}</code></pre>"
        if raw.startswith("`"):
            return f"<code>{html.escape(raw[1:-1])}</code>"
        return html.escape(raw)  # math: escaped text, MathJax reads DOM text

    return re.sub(r"\x00(\d+)\x00", unstash, text)


def _inline(text):
    def _link(m):
        label, url = m.group(1), m.group(2)
        if url.startswith("file://"):
            fail(f"local file:// URL is forbidden in public site content: {url!r}")
        return f'<a href="{url}">{label}</a>'
    text = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)", _link, text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"(?<!\*)\*([^*\n]+)\*(?!\*)", r"<em>\1</em>", text)
    return text


def md_to_html(body):
    store = []
    body = _protect(body, store)
    body = html.escape(body, quote=False)
    out, i = [], 0
    lines = body.split("\n")
    n = len(lines)
    while i < n:
        line = lines[i]
        s = line.strip()
        if not s:
            i += 1
            continue
        if re.fullmatch(r"-{3,}", s):
            out.append("<hr>")
            i += 1
        elif s.startswith("#"):
            level = len(s) - len(s.lstrip("#"))
            out.append(f"<h{level}>{_inline(s[level:].strip())}</h{level}>")
            i += 1
        elif s.startswith("|"):
            rows = []
            while i < n and lines[i].strip().startswith("|"):
                cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
                if not all(re.fullmatch(r":?-+:?", c) for c in cells):
                    rows.append(cells)
                i += 1
            thead = "".join(f"<th>{_inline(c)}</th>" for c in rows[0])
            tbody = "".join(
                "<tr>" + "".join(f"<td>{_inline(c)}</td>" for c in r) + "</tr>"
                for r in rows[1:]
            )
            out.append(
                f'<div class="tablewrap"><table><thead><tr>{thead}</tr></thead>'
                f"<tbody>{tbody}</tbody></table></div>"
            )
        elif s.startswith("&gt;"):
            quote = []
            while i < n and lines[i].strip().startswith("&gt;"):
                quote.append(lines[i].strip()[4:].strip())
                i += 1
            out.append(f"<blockquote><p>{_inline(' '.join(quote))}</p></blockquote>")
        elif re.match(r"^[-*] ", s) or re.match(r"^\d+\. ", s):
            ordered = bool(re.match(r"^\d+\. ", s))
            start = int(re.match(r"^(\d+)\. ", s).group(1)) if ordered else 1
            items, current = [], None
            pat = r"^\d+\. " if ordered else r"^[-*] "
            while i < n:
                ls = lines[i].strip()
                if re.match(pat, ls):
                    if current is not None:
                        items.append(current)
                    current = re.sub(pat, "", ls)
                elif ls and lines[i].startswith((" ", "\t")):
                    current += " " + ls  # continuation line
                else:
                    break
                i += 1
            items.append(current)
            tag = "ol" if ordered else "ul"
            attr = f' start="{start}"' if ordered and start != 1 else ""
            out.append(
                f"<{tag}{attr}>" + "".join(f"<li>{_inline(it)}</li>" for it in items) + f"</{tag}>"
            )
        else:
            para = []
            while i < n and lines[i].strip() and not re.match(
                r"^(#|\||&gt;|[-*] |\d+\. |-{3,}$)", lines[i].strip()
            ):
                para.append(lines[i].strip())
                i += 1
            out.append(f"<p>{_inline(' '.join(para))}</p>")
    return _restore("\n".join(out), store)


# ---------------------------------------------------------------- Lean helpers

def _strip_lean_comments(text):
    """Strip Lean `/- ... -/` block comments (nested) and `-- ...` line comments, preserving line count."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text[i:i + 2] == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and text[i:i + 2] == "-/":
            depth -= 1
            i += 2
        else:
            ch = text[i]
            out.append(ch if depth == 0 or ch == "\n" else " ")
            i += 1
    return "".join(out)


def _find_top_level_assign(line):
    """Return index of a declaration-level `:=` in `line`, ignoring `let`/`letI`/`have` bindings."""
    stripped = line.lstrip()
    if re.match(r"^(?:let|letI|have|haveI)\b", stripped):
        return -1
    # Ignore `:=` that follows a `let ` on the same line (e.g. `∃ ..., let x := ...`)
    m_let = re.search(r"\b(?:let|letI)\b", line)
    pos = line.find(" :=")
    if pos == -1:
        return -1
    if m_let and m_let.start() < pos:
        return -1
    return pos


def extract_lean_declaration(rel_path, decl_name):
    """Find `decl_name` in `rel_path` and return `(line_no, signature_snippet)`."""
    p = ROOT / rel_path
    if not p.is_file():
        fail(f"solved_catalog: Lean file {rel_path!r} does not exist")
    lines = p.read_text(encoding="utf-8").splitlines()
    pat = re.compile(
        rf"^(?:@\[[^\]]+\]\s+)?(?:protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def)\s+{re.escape(decl_name)}\b"
    )
    for idx, line in enumerate(lines):
        if pat.match(line):
            sig_lines = []
            for j in range(idx, min(idx + 24, len(lines))):
                cur = lines[j]
                if j > idx and re.match(r"^\s*\|", cur):
                    # Pattern-matching equation compiler arms (`| 0 => ...`) start the proof/body
                    sig_lines.append("  | …")
                    break
                if " := by" in cur:
                    sig_lines.append(cur.split(" := by", 1)[0] + " := by …")
                    break
                if cur.rstrip().endswith(":= by"):
                    sig_lines.append(cur + " …")
                    break
                assign_pos = _find_top_level_assign(cur)
                if assign_pos != -1:
                    sig_lines.append(cur[:assign_pos] + " := …")
                    break
                sig_lines.append(cur)
                if cur.strip().endswith("where"):
                    break
            return idx + 1, "\n".join(sig_lines)
    fail(f"solved_catalog: declaration {decl_name!r} not found in {rel_path!r}")


_THEOREM_LINE_RE = re.compile(
    r"^(?:@\[[^\]]+\]\s+)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+[A-Za-z0-9_']+\b"
)
_PUBLIC_THEOREM_LINE_RE = re.compile(
    r"^(?:@\[[^\]]+\]\s+)?(?:protected\s+)?(?:theorem|lemma)\s+[A-Za-z0-9_']+\b"
)


def count_proved_lean_theorems():
    """Count source-level `theorem`/`lemma` declarations across Known/ and Bridge/
    (stripping comments and excluding 0-theorem import barrels)."""
    total = 0
    proof_files = 0
    for base in (ROOT / "lean" / "InfoTheory" / "Bridge", ROOT / "lean" / "InfoTheory" / "Known"):
        if base.is_dir():
            for f in sorted(base.rglob("*.lean")):
                cleaned = _strip_lean_comments(f.read_text(encoding="utf-8"))
                n_in_file = sum(1 for line in cleaned.splitlines() if _THEOREM_LINE_RE.match(line))
                if n_in_file > 0:
                    proof_files += 1
                    total += n_in_file
    return total, proof_files


def load_certificate_info(short_mod):
    cert_path = LEAN_CERTS_DIR / f"{short_mod}.lean"
    if not cert_path.is_file():
        return None
    text = cert_path.read_text(encoding="utf-8")
    cleaned_lines = _strip_lean_comments(text).splitlines()
    rel_path = f"lean/InfoTheory/Known/Certificates/{short_mod}.lean"
    doc_match = re.search(r"/-!(.*?)-/", text, flags=re.S)
    doc = doc_match.group(1).strip() if doc_match else ""
    decls = []
    for idx, line in enumerate(cleaned_lines, 1):
        if _PUBLIC_THEOREM_LINE_RE.match(line):
            m = re.search(r"\b(?:theorem|lemma)\s+([A-Za-z0-9_']+)\b", line)
            if m:
                decls.append((m.group(1), idx))
    decl_names = {name for name, _ in decls}
    settled_kind = None
    if "statement_false" in decl_names:
        settled_kind = "false"
    elif "statement_true" in decl_names:
        settled_kind = "true"
    return {
        "file": rel_path,
        "module": f"InfoTheory.Known.Certificates.{short_mod}",
        "doc": doc,
        "decls": decls,
        "settled_kind": settled_kind,
        "code": text.strip(),
    }


# ---------------------------------------------------------------- templates

MATHJAX = (
    '<script>MathJax={tex:{inlineMath:[["$","$"],["\\\\(","\\\\)"]]}};</script>'
    '<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>'
)


def make_filter_js(noun="problems", has_cert=False):
    cert_var = "let activeCert = 'all';" if has_cert else ""
    cert_cond = "const okCert = activeCert === 'all' || c.dataset.cert === activeCert;" if has_cert else "const okCert = true;"
    cert_bind = """
  document.querySelectorAll('[data-filter-cert]').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('[data-filter-cert]').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      activeCert = btn.dataset.filterCert;
      apply();
    });
  });""" if has_cert else ""
    return f"""<script>
(function(){{
  const q = document.getElementById('search');
  const cards = Array.from(document.querySelectorAll('.card[data-cat]'));
  const countEl = document.getElementById('match-count');
  let activeCat = 'all', activeStatus = 'all';
  {cert_var}

  function apply(){{
    const term = (q && q.value ? q.value : '').trim().toLowerCase();
    let shown = 0;
    for (const c of cards){{
      const okCat = activeCat === 'all' || c.dataset.cat === activeCat;
      const okSt = activeStatus === 'all' || (c.dataset.status || 'all') === activeStatus;
      {cert_cond}
      const okQ = !term || (c.dataset.search || '').includes(term);
      const show = okCat && okSt && okCert && okQ;
      c.style.display = show ? '' : 'none';
      if (show) shown++;
    }}
    if (countEl) countEl.textContent = shown + ' of ' + cards.length + ' {noun} shown';
  }}

  document.querySelectorAll('[data-filter-cat]').forEach(btn => {{
    btn.addEventListener('click', () => {{
      document.querySelectorAll('[data-filter-cat]').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      activeCat = btn.dataset.filterCat;
      apply();
    }});
  }});

  document.querySelectorAll('[data-filter-status]').forEach(btn => {{
    btn.addEventListener('click', () => {{
      document.querySelectorAll('[data-filter-status]').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      activeStatus = btn.dataset.filterStatus;
      apply();
    }});
  }});{cert_bind}

  if (q) q.addEventListener('input', apply);
  apply();
}})();
</script>"""


def page(title, body_html, depth=0, active="open", extra_js=""):
    rel = "../" * depth
    cls_open = ' class="nav-active"' if active == "open" else ""
    cls_solved = ' class="nav-active"' if active == "solved" else ""
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<link rel="stylesheet" href="{rel}style.css">
{MATHJAX}
</head>
<body>
<header>
  <nav class="header-nav">
    <a href="{rel}index.html"{cls_open}>Open Problems in Information Theory</a>
    <a href="{rel}solved/index.html"{cls_solved}>Solved Problems: Lean Proofs</a>
  </nav>
  <span class="header-note">Lean 4 Verified · 0 sorry · Standard Axioms</span>
</header>
<main>
{body_html}
</main>
<footer>Maintained on <a href="https://github.com/gokhanmergen/information-theory-problems">GitHub</a> — problems, Lean 4 formalizations, corrections, and proofs (human or AI) welcome by pull request.</footer>
{extra_js}
</body>
</html>
"""


def badge(status):
    label = STATUS_LABELS.get(status, status)
    return f'<span class="badge badge-{html.escape(status)}">{html.escape(label)}</span>'


def formal_status_badge(formal_status):
    if not formal_status:
        return ""
    if formal_status not in FORMAL_STATUS_META:
        fail(f"unknown formal_status {formal_status!r}; expected one of {sorted(FORMAL_STATUS_META)}")
    label, _ = FORMAL_STATUS_META[formal_status]
    return f'<span class="badge badge-formal-{html.escape(formal_status)}">{html.escape(label)}</span>'


def load_attempts(problem_id):
    adir = ROOT / "attempts" / problem_id
    if not adir.is_dir():
        return []
    attempts = []
    for f in sorted(adir.glob("*.md")):
        meta, body = parse_frontmatter(f)
        if meta.get("problem") != problem_id:
            fail(f"{f}: frontmatter problem={meta.get('problem')!r} != dir {problem_id!r}")
        attempts.append((f.name, meta, body))
    return attempts


def load_lean_info(meta):
    lean_file = meta.get("lean_file", "")
    lean_module = meta.get("lean_module", "")
    if not lean_file:
        return None
    p = ROOT / lean_file
    if not p.is_file():
        fail(f"{meta['id']}: lean_file {lean_file!r} does not exist")
    short_mod = lean_module.split(".")[-1] if lean_module else p.stem
    sol_file = LEAN_SOLUTIONS_DIR / f"{short_mod}.lean"
    return {
        "file": lean_file,
        "module": lean_module,
        "short_mod": short_mod,
        "code": p.read_text(encoding="utf-8").strip(),
        "has_solution": sol_file.is_file(),
        "solution_file": f"lean/InfoTheory/Solutions/{short_mod}.lean",
        "cert": load_certificate_info(short_mod),
    }


def main():
    problems = []
    problems_by_id = {}
    for f in sorted((ROOT / "problems").glob("*.md")):
        meta, body = parse_frontmatter(f)
        for key in ("id", "title", "status"):
            if key not in meta:
                fail(f"{f}: missing frontmatter key {key!r}")
        if meta["id"] != f.stem:
            fail(f"{f}: id {meta['id']!r} != filename stem")
        lean_info = load_lean_info(meta)
        rec = (meta, body, load_attempts(meta["id"]), lean_info)
        problems.append(rec)
        problems_by_id[meta["id"]] = rec

    # Validate solved catalog and build reverse map open_id -> [(solved_entry, relation)]
    solved_entries = []
    open_to_solved = {pid: [] for pid in problems_by_id}
    seen_solved_ids = set()
    for entry in SOLVED_THEOREMS:
        sid = entry["id"]
        if sid in seen_solved_ids:
            fail(f"solved_catalog: duplicate solved id {sid!r}")
        seen_solved_ids.add(sid)
        resolved_decls = []
        for rel_path, decl_name in entry["lean_decls"]:
            line_no, sig = extract_lean_declaration(rel_path, decl_name)
            resolved_decls.append((rel_path, decl_name, line_no, sig))
        for oid in entry["related_open"]:
            if oid not in problems_by_id:
                fail(f"solved_catalog: {sid!r} references unknown open problem {oid!r}")
            open_to_solved[oid].append((entry, "direct"))
        for oid in entry.get("analogous_open", []):
            if oid not in problems_by_id:
                fail(f"solved_catalog: {sid!r} references unknown analogous open problem {oid!r}")
            open_to_solved[oid].append((entry, "analogous"))
        solved_entries.append({**entry, "resolved_decls": resolved_decls})

    n_proved_decls, n_proof_files = count_proved_lean_theorems()

    if SITE.exists():
        shutil.rmtree(SITE)
    (SITE / "problems").mkdir(parents=True)
    (SITE / "solved").mkdir(parents=True)
    shutil.copy(ROOT / "static" / "style.css", SITE / "style.css")

    # Stats
    n_total = len(problems)
    n_open = sum(1 for m, _, _, _ in problems if m["status"] in ("open", "partially-solved"))
    n_solved_open_cat = sum(1 for m, _, _, _ in problems if m["status"] == "solved")
    n_lean = sum(1 for _, _, _, l in problems if l is not None)
    n_certified = sum(
        1 for _, _, _, l in problems
        if l is not None and l["cert"] is not None and l["cert"]["settled_kind"] is None
    )
    n_classical = len(solved_entries)

    # ------------------------------------------------------------ Open Problems Index
    cat_counts = {}
    for m, _, _, _ in problems:
        c = m.get("category", "uncategorized")
        cat_counts[c] = cat_counts.get(c, 0) + 1

    rows = []
    for meta, _, attempts, lean_info in problems:
        cat = meta.get("category", "uncategorized")
        cat_label = CATEGORY_LABELS.get(cat, cat)
        tags = " ".join(f'<span class="tag">{html.escape(t)}</span>' for t in meta.get("tags", []))
        posed = html.escape(meta.get("posed_year", ""))
        att = f'{len(attempts)} attempt{"s" if len(attempts) != 1 else ""}' if attempts else "no attempts yet"
        n_rel_solved = len(open_to_solved[meta["id"]])
        rel_note = (
            f' · {n_rel_solved} related Lean proof{"s" if n_rel_solved != 1 else ""}'
            if n_rel_solved
            else ""
        )
        badges = []
        if lean_info:
            if lean_info["has_solution"]:
                badges.append('<span class="badge badge-lean-verified">Lean 4 proof</span>')
            else:
                badges.append('<span class="badge badge-lean">Lean 4</span>')
            if lean_info["cert"]:
                if lean_info["cert"]["settled_kind"] is None:
                    badges.append('<span class="badge badge-certified">Certified</span>')
                else:
                    badges.append('<span class="badge badge-partially-solved">Statement bug</span>')
        if meta.get("formal_status"):
            badges.append(formal_status_badge(meta["formal_status"]))
        badges.append(badge(meta["status"]))
        has_cert = "yes" if (lean_info and lean_info["cert"] and lean_info["cert"]["settled_kind"] is None) else "no"
        search_blob = " ".join([
            meta["id"], meta["title"], meta.get("posed_by", ""),
            cat, cat_label, " ".join(meta.get("tags", [])),
            "certified" if has_cert == "yes" else "",
            meta.get("formal_status", ""),
        ]).lower()
        rows.append(
            f'<a class="card" href="problems/{meta["id"]}.html" '
            f'data-cat="{html.escape(cat)}" data-status="{html.escape(meta["status"])}" '
            f'data-cert="{has_cert}" data-search="{html.escape(search_blob)}">'
            f'<div class="card-top"><h2>{html.escape(meta["title"])}</h2>'
            f'<div class="badges">{"".join(badges)}</div></div>'
            f'<div class="card-meta">{html.escape(cat_label)} · '
            f'{f"posed {posed} · " if posed else ""}{att}{rel_note}</div>'
            f'<div class="tags">{tags}</div></a>'
        )

    cat_buttons = ['<button class="pill active" data-filter-cat="all">All (' + str(n_total) + ')</button>']
    for cat_key, cat_label in CATEGORY_LABELS.items():
        if cat_key in cat_counts:
            cat_buttons.append(
                f'<button class="pill" data-filter-cat="{html.escape(cat_key)}">'
                f'{html.escape(cat_label)} ({cat_counts[cat_key]})</button>'
            )

    status_buttons = [
        '<button class="pill active" data-filter-status="all">All statuses</button>',
        '<button class="pill" data-filter-status="open">Open</button>',
        '<button class="pill" data-filter-status="partially-solved">Partially solved</button>',
        '<button class="pill" data-filter-status="solved">Solved</button>',
        f'<button class="pill" data-filter-cert="yes">Certified bounds ({n_certified})</button>',
        '<button class="pill active" data-filter-cert="all">All certification</button>',
    ]

    intro = (
        "<h1>Open Problems in Information Theory</h1>"
        f"<p class='lede'>A curated, Lean 4–formalized catalog of <strong>{n_open} open problems</strong> "
        f"({n_total} total, {n_lean} with machine-checked Lean 4 statements), in the spirit of "
        '<a href="https://www.erdosproblems.com/">erdosproblems.com</a>. '
        "Provability comes for free via Lean: submit a proof of <code>Statement</code> (or "
        "<code>¬ Statement</code>) under <code>lean/InfoTheory/Solutions/</code> and run "
        "<code>python3 scripts/verify_proof.py --verify &lt;id&gt;</code>.</p>"
        '<div class="sister-banner">'
        f'<span><strong>Sister Catalog:</strong> {n_classical} classical theorems &amp; '
        f'{n_certified} certified open-problem bounds ({n_proved_decls} proved Lean 4 theorems, 0 sorry).</span>'
        '<a href="solved/index.html">Browse Solved Problems: Lean Proofs →</a>'
        '</div>'
        '<div class="stats">'
        f'<div class="stat"><span class="stat-num">{n_open}</span><span class="stat-lbl">Open / Partial</span></div>'
        f'<div class="stat"><span class="stat-num">{n_lean}</span><span class="stat-lbl">Lean 4 Statements</span></div>'
        f'<div class="stat"><span class="stat-num">{n_certified}/{n_total}</span><span class="stat-lbl">Certified Bounds</span></div>'
        f'<div class="stat"><span class="stat-num">{n_proved_decls}</span><span class="stat-lbl">Proved Lean Theorems</span></div>'
        '</div>'
        '<div class="controls">'
        '<input id="search" type="search" placeholder="Search open problems by title, author, tag, or subfield…">'
        f'<div class="pill-row">{"".join(status_buttons[:4])}</div>'
        f'<div class="pill-row">{"".join(status_buttons[5:])}{status_buttons[4]}</div>'
        f'<div class="pill-row">{"".join(cat_buttons)}</div>'
        '<div id="match-count" class="match-count"></div>'
        '</div>'
    )
    (SITE / "index.html").write_text(
        page(
            "Open Problems in Information Theory",
            intro + "\n".join(rows),
            depth=0,
            active="open",
            extra_js=make_filter_js("problems", has_cert=True),
        ),
        encoding="utf-8",
    )

    # ------------------------------------------------------------ Open Problem Pages
    for meta, body, attempts, lean_info in problems:
        badges = []
        if lean_info:
            if lean_info["has_solution"]:
                badges.append('<span class="badge badge-lean-verified">Lean 4 proof</span>')
            else:
                badges.append('<span class="badge badge-lean">Lean 4</span>')
            if lean_info["cert"]:
                badges.append('<span class="badge badge-certified">Certified bounds</span>')
        if meta.get("formal_status"):
            badges.append(formal_status_badge(meta["formal_status"]))
        badges.append(badge(meta["status"]))
        parts = [
            f'<div class="card-top"><h1>{html.escape(meta["title"])}</h1>'
            f'<div class="badges">{"".join(badges)}</div></div>'
        ]
        posed_by, posed_year = meta.get("posed_by", ""), meta.get("posed_year", "")
        cat = meta.get("category", "")
        cat_label = CATEGORY_LABELS.get(cat, cat)
        prov_bits = []
        if posed_by or posed_year:
            prov_bits.append(f"Posed by {posed_by}" + (f", {posed_year}" if posed_year else ""))
        if cat_label:
            prov_bits.append(cat_label)
        if prov_bits:
            parts.append(f'<p class="provenance">{html.escape(" · ".join(prov_bits))}.</p>')
        fs = meta.get("formal_status")
        if fs:
            fs_label, fs_desc = FORMAL_STATUS_META[fs]
            note = meta.get("formal_status_note", "")
            extra = f" — {html.escape(note)}" if note else ""
            parts.append(
                f'<div class="formal-status-banner formal-{html.escape(fs)}">'
                f'<strong>Formalization status ({html.escape(fs_label)}):</strong> '
                f'{html.escape(fs_desc)}{extra}</div>'
            )

        parts.append(md_to_html(body))

        # Related Solved Theorems (reverse cross-links!)
        rel_solved = open_to_solved[meta["id"]]
        if rel_solved:
            parts.append("<h2>Related Solved Theorems (Lean 4 Proofs)</h2>")
            parts.append(
                '<p class="muted">Machine-checked classical theorems in this codebase related to '
                'this open problem (labeled <em>direct</em> vs. <em>analogous</em>):</p>'
            )
            cards = []
            for se, rel_kind in rel_solved:
                scat = SOLVED_CATEGORY_LABELS.get(se["category"], se["category"])
                rel_badge = (
                    '<span class="badge badge-solved">direct</span>'
                    if rel_kind == "direct"
                    else '<span class="badge badge-partially-solved">analogous</span>'
                )
                cards.append(
                    f'<a class="crosslink-card" href="../solved/{html.escape(se["id"])}.html">'
                    f'<span class="crosslink-title">{html.escape(se["title"])}</span>'
                    f'<span class="crosslink-meta"><span>{html.escape(scat)}</span>'
                    f'{rel_badge}</span></a>'
                )
            parts.append(f'<div class="crosslink-grid">{"".join(cards)}</div>')
        else:
            parts.append("<h2>Related Solved Theorems (Lean 4 Proofs)</h2>")
            parts.append(
                '<p class="muted">No directly linked classical Lean proof in the '
                '<a href="../solved/index.html">Solved Problems</a> catalog yet.</p>'
            )

        # Machine-checked Certificate for this open problem (if present)
        if lean_info and lean_info["cert"]:
            cert = lean_info["cert"]
            parts.append("<h2>Certified Known Bounds (Lean 4)</h2>")
            cert_url = f'{GITHUB_BLOB}/{cert["file"]}'
            decl_links = ", ".join(
                f'<a href="{cert_url}#L{ln}"><code>{html.escape(dn)}</code></a>'
                for dn, ln in cert["decls"][:12]
            )
            if len(cert["decls"]) > 12:
                decl_links += f' (+{len(cert["decls"]) - 12} more)'
            parts.append(
                '<div class="cert-box">'
                f'<p>Module <code>{html.escape(cert["module"])}</code> '
                f'(<a href="{cert_url}">{html.escape(cert["file"])}</a>) '
                f'machine-checks <strong>{len(cert["decls"])}</strong> known-bound theorem'
                f'{"s" if len(cert["decls"]) != 1 else ""} directly about this frozen <code>Statement</code> '
                f'(standard axioms only, replayed by <code>leanchecker</code>).</p>'
                f'<p class="muted">Certified declarations: {decl_links}</p>'
                f'<details class="attempt"><summary>View certificate Lean 4 source ({len(cert["decls"])} theorems)</summary>'
                f'<div class="attempt-body"><pre class="lean-code"><code>{html.escape(cert["code"])}</code></pre></div>'
                '</details></div>'
            )

        if lean_info:
            parts.append("<h2>Lean 4 Formalization</h2>")
            src_url = f'{GITHUB_BLOB}/{lean_info["file"]}'
            parts.append(
                f'<p class="muted">Module <code>{html.escape(lean_info["module"])}</code> '
                f'(<a href="{src_url}"><code>{html.escape(lean_info["file"])}</code></a>). '
                f'To certify a proof or disproof mechanically, add '
                f'<code>{html.escape(lean_info["solution_file"])}</code> defining '
                f'<code>proof : {html.escape(lean_info["module"])}.Statement</code> (or '
                f'<code>disproof : ¬ {html.escape(lean_info["module"])}.Statement</code>) and run '
                f'<code>python3 scripts/verify_proof.py --verify {html.escape(meta["id"])}</code>.</p>'
            )
            parts.append(f'<pre class="lean-code"><code>{html.escape(lean_info["code"])}</code></pre>')

        parts.append(f"<h2>Attempts ({len(attempts)})</h2>")
        if not attempts:
            parts.append(
                '<p class="muted">No attempts recorded yet. See AGENTS.md in the repository for the attempt protocol.</p>'
            )
        for name, ameta, abody in attempts:
            head = (
                f'<span class="att-who">{html.escape(ameta.get("attempter", "?"))}</span> '
                f'<span class="muted">{html.escape(ameta.get("date", ""))}'
                f'{" · " + html.escape(ameta["model"]) if ameta.get("model") else ""}</span> '
                f'<span class="tag">{html.escape(ameta.get("type", ""))}</span> '
                f'<span class="tag tag-status">{html.escape(ameta.get("status", ""))}</span>'
            )
            parts.append(
                f'<details class="attempt"><summary>{head}</summary>'
                f'<div class="attempt-body">{md_to_html(abody)}'
                f'<p class="muted">source: attempts/{html.escape(meta["id"])}/{html.escape(name)}</p>'
                f"</div></details>"
            )
        (SITE / "problems" / f'{meta["id"]}.html').write_text(
            page(meta["title"], "\n".join(parts), depth=1, active="open"), encoding="utf-8"
        )

    # ------------------------------------------------------------ Solved Problems Index
    solved_cat_counts = {}
    for se in solved_entries:
        c = se["category"]
        solved_cat_counts[c] = solved_cat_counts.get(c, 0) + 1

    solved_rows = []
    for se in solved_entries:
        cat = se["category"]
        cat_label = SOLVED_CATEGORY_LABELS.get(cat, cat)
        tags = " ".join(f'<span class="tag">{html.escape(t)}</span>' for t in se["tags"])
        n_decls = len(se["resolved_decls"])
        n_rel = len(se["related_open"]) + len(se.get("analogous_open", []))
        files_used = sorted({rp.replace("lean/InfoTheory/", "") for rp, _, _, _ in se["resolved_decls"]})
        files_str = ", ".join(files_used)
        search_blob = " ".join([
            se["id"], se["title"], se["authors"], se["reference"],
            cat, cat_label, " ".join(se["tags"]),
            " ".join(dn for _, dn, _, _ in se["resolved_decls"]),
            " ".join(se["related_open"]),
            " ".join(se.get("analogous_open", [])),
        ]).lower()
        solved_rows.append(
            f'<a class="card" href="{html.escape(se["id"])}.html" '
            f'data-cat="{html.escape(cat)}" data-status="solved" '
            f'data-search="{html.escape(search_blob)}">'
            f'<div class="card-top"><h2>{html.escape(se["title"])}</h2>'
            f'<div class="badges"><span class="badge badge-lean-verified">Lean 4 proved</span></div></div>'
            f'<div class="card-meta">{html.escape(cat_label)} · {html.escape(se["year"])} · '
            f'{n_decls} key declaration{"s" if n_decls != 1 else ""} ({html.escape(files_str)}) · '
            f'links to {n_rel} open problem{"s" if n_rel != 1 else ""}</div>'
            f'<div class="tags">{tags}</div></a>'
        )

    solved_cat_buttons = [
        f'<button class="pill active" data-filter-cat="all">All ({n_classical})</button>'
    ]
    for cat_key, cat_label in SOLVED_CATEGORY_LABELS.items():
        if cat_key in solved_cat_counts:
            solved_cat_buttons.append(
                f'<button class="pill" data-filter-cat="{html.escape(cat_key)}">'
                f'{html.escape(cat_label)} ({solved_cat_counts[cat_key]})</button>'
            )

    # Certified open-problem bounds section on Solved Index
    cert_cards = []
    for meta, _, _, lean_info in problems:
        if lean_info and lean_info["cert"] and lean_info["cert"]["settled_kind"] is None:
            cert = lean_info["cert"]
            cert_url = f'{GITHUB_BLOB}/{cert["file"]}'
            cert_cards.append(
                f'<div class="crosslink-card">'
                f'<a class="crosslink-title" href="../problems/{html.escape(meta["id"])}.html">'
                f'{html.escape(meta["title"])}</a>'
                f'<div class="crosslink-meta">'
                f'<a href="{cert_url}"><code>{html.escape(lean_info["short_mod"])}.lean</code> ({len(cert["decls"])} theorems)</a>'
                f'{badge(meta["status"])}'
                f'</div></div>'
            )

    solved_intro = (
        "<h1>Solved Problems in Information Theory: Lean Proofs</h1>"
        f"<p class='lede'>Machine-checked Lean 4 proofs of <strong>{n_classical} classical theorems</strong> "
        f"spanning Cover &amp; Thomas (<em>Elements of Information Theory</em>), El Gamal &amp; Kim "
        f"(<em>Network Information Theory</em>), Yeung, Gallager, Lovász, and classical coding theory — "
        f"comprising <strong>{n_proved_decls} proved theorems</strong> across <strong>{n_proof_files} Lean modules</strong> "
        f"with <strong>zero <code>sorry</code></strong>, standard axioms only "
        f"(<code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>), "
        f"and full <code>leanchecker</code> kernel replay.</p>"
        '<div class="sister-banner">'
        f'<span><strong>Sister Catalog:</strong> {n_open} open problems formalized in Lean 4, '
        f'bidirectionally linked to the classical proofs below.</span>'
        '<a href="../index.html">← Browse Open Problems in Information Theory</a>'
        '</div>'
        '<div class="stats">'
        f'<div class="stat"><span class="stat-num">{n_classical}</span><span class="stat-lbl">Classical Theorems</span></div>'
        f'<div class="stat"><span class="stat-num">{n_proved_decls}</span><span class="stat-lbl">Lean 4 Theorems</span></div>'
        f'<div class="stat"><span class="stat-num">{n_proof_files}</span><span class="stat-lbl">Lean Proof Modules</span></div>'
        f'<div class="stat"><span class="stat-num">{n_certified}/{n_total}</span><span class="stat-lbl">Certified Open Bounds</span></div>'
        '</div>'
        '<div class="controls">'
        '<input id="search" type="search" placeholder="Search solved theorems by title, author, chapter, Lean name, or open problem…">'
        f'<div class="pill-row">{"".join(solved_cat_buttons)}</div>'
        '<div id="match-count" class="match-count"></div>'
        '</div>'
    )

    cert_section = (
        f"<h2>Certified Known Bounds on Open Problems ({n_certified}/{n_total})</h2>"
        '<p class="muted">In addition to the standalone classical theorems above, the following '
        'machine-checked certificate modules under <code>lean/InfoTheory/Known/Certificates/</code> '
        'prove the textbook upper/lower bounds claimed in the docstrings of our frozen open-problem '
        'statements — verifying non-vacuity directly against the exact Lean objects in each '
        '<code>Statement</code>.</p>'
        f'<div class="crosslink-grid">{"".join(cert_cards)}</div>'
    )

    (SITE / "solved" / "index.html").write_text(
        page(
            "Solved Problems in Information Theory: Lean Proofs",
            solved_intro + "\n".join(solved_rows) + cert_section,
            depth=1,
            active="solved",
            extra_js=make_filter_js("classical theorems", has_cert=False),
        ),
        encoding="utf-8",
    )

    # ------------------------------------------------------------ Individual Solved Theorem Pages
    for se in solved_entries:
        cat_label = SOLVED_CATEGORY_LABELS.get(se["category"], se["category"])
        sparts = [
            f'<div class="card-top"><h1>{html.escape(se["title"])}</h1>'
            f'<div class="badges"><span class="badge badge-lean-verified">Lean 4 proved</span></div></div>',
            f'<p class="provenance">{html.escape(se["authors"])} ({html.escape(se["year"])}) · '
            f'{html.escape(cat_label)} · {html.escape(se["reference"])}.</p>',
            "<h2>Theorem Statement</h2>",
            md_to_html(se["statement"]),
            "<h2>Proof Overview</h2>",
            md_to_html(se["proof_notes"]),
            f'<h2>Lean 4 Machine-Checked Declarations ({len(se["resolved_decls"])})</h2>',
            '<p class="muted">All declarations below are compiled in Lean 4 (v4.36.0), verified to depend '
            'exclusively on <code>[propext, Classical.choice, Quot.sound]</code> via '
            '<code>scripts/AuditKnown.lean</code>, and kernel-replayed by <code>leanchecker</code>.</p>',
        ]

        decl_items = []
        for rel_path, decl_name, line_no, sig in se["resolved_decls"]:
            url = f"{GITHUB_BLOB}/{rel_path}#L{line_no}"
            mod_name = rel_path.replace("lean/", "").replace(".lean", "").replace("/", ".")
            decl_items.append(
                "<li>"
                '<div class="decl-head">'
                f'<strong><code>{html.escape(decl_name)}</code></strong>'
                f'<a href="{url}">{html.escape(mod_name)} (line {line_no}) ↗</a>'
                "</div>"
                f'<pre class="lean-code decl-sig"><code>{html.escape(sig)}</code></pre>'
                "</li>"
            )
        sparts.append(f'<ul class="decl-list">{"".join(decl_items)}</ul>')

        # Cross-links to Open Problems
        direct_open = se["related_open"]
        analog_open = se.get("analogous_open", [])
        n_total_open_links = len(direct_open) + len(analog_open)
        if n_total_open_links:
            sparts.append(f'<h2>Related Open Problems ({n_total_open_links})</h2>')
            sparts.append(
                '<p class="muted">Open problems in the sister catalog that build on, generalize, or '
                'are analogous to this classical theorem:</p>'
            )
            ocards = []
            for oid, rel_kind in [(o, "direct") for o in direct_open] + [(o, "analogous") for o in analog_open]:
                ometa, _, _, olean = problems_by_id[oid]
                ocat = CATEGORY_LABELS.get(ometa.get("category", ""), ometa.get("category", ""))
                cert_tag = (
                    ' <span class="badge badge-certified">Certified</span>'
                    if (olean and olean["cert"])
                    else ""
                )
                kind_tag = (
                    ' <span class="badge badge-partially-solved">analogous</span>'
                    if rel_kind == "analogous"
                    else ""
                )
                ocards.append(
                    f'<a class="crosslink-card" href="../problems/{html.escape(oid)}.html">'
                    f'<span class="crosslink-title">{html.escape(ometa["title"])}</span>'
                    f'<span class="crosslink-meta"><span>{html.escape(ocat)}</span>'
                    f'<span>{kind_tag}{cert_tag}{badge(ometa["status"])}</span></span></a>'
                )
            sparts.append(f'<div class="crosslink-grid">{"".join(ocards)}</div>')

        sparts.append(
            '<p class="muted"><a href="index.html">← All Solved Problems: Lean Proofs</a> · '
            '<a href="../index.html">Open Problems in Information Theory</a></p>'
        )

        (SITE / "solved" / f'{se["id"]}.html').write_text(
            page(
                f'{se["title"]} — Solved Problems in Information Theory',
                "\n".join(sparts),
                depth=1,
                active="solved",
            ),
            encoding="utf-8",
        )

    # Post-render privacy guard: refuse any file:// or local home-directory path anywhere in site/
    for html_file in sorted(SITE.rglob("*.html")):
        rendered = html_file.read_text(encoding="utf-8")
        if re.search(r"file://", rendered, flags=re.I) or "/Users/" in rendered:
            fail(f"local path / file:// leak detected in rendered HTML: {html_file}")

    print(
        f"built site/ — {n_total} open-catalog problems ({n_open} open/partial, {n_solved_open_cat} solved, "
        f"{n_lean} Lean 4 formalized, {n_certified} certified), "
        f"{n_classical} classical solved theorems ({n_proved_decls} source-level theorem/lemma declarations across {n_proof_files} modules), "
        f"{sum(len(a) for _, _, a, _ in problems)} attempts"
    )


if __name__ == "__main__":
    main()
