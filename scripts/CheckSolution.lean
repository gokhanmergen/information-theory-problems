/-
Trusted Lean 4 solution checker.
Usage:
  lake env lean --run ../scripts/CheckSolution.lean <ProblemModule> <SolutionModule>

Security properties:
1. Loads the compiled `.olean` environment directly with `trustLevel := 0` (no user
   syntax or custom elaborators from the solution module are ever executed, preventing
   `#print axioms` spoofing).
2. Verifies `<ProblemModule>.Statement` is declared in `<ProblemModule>` and has type `Prop`.
3. Requires the solution module to declare *exactly one* of `proof` or `disproof` in
   `<SolutionModule>`, as an actual theorem or definition (not an `axiom` or `opaque`).
4. Verifies its type is *syntactically* `<ProblemModule>.Statement` (resp. `¬ …`),
   with no universe parameters (`levelParams.isEmpty`).
5. Walks the entire transitive constant closure — explicitly inspecting `.thmInfo` proof
   bodies, `.defnInfo` bodies, and `.opaqueInfo` bodies — and rejects any axiom outside
   `{propext, Classical.choice, Quot.sound}` (catching `sorryAx`, custom axioms,
   `Lean.ofReduceBool`, `Lean.trustCompiler`, etc.).

Kernel re-checking (catching `debug.skipKernelTC` forgeries) is performed separately by
`lake env leanchecker <SolutionModule>`. Both checks must pass.
-/
import Lean
open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

partial def collectAxioms (env : Environment) (n : Name) : StateM (NameSet × Array Name) Unit := do
  let (seen, axs) ← get
  if seen.contains n then return
  set (seen.insert n, axs)
  match env.find? n with
  | none =>
    modify fun (s, a) => (s, a.push (`__missing__ ++ n))
  | some ci =>
    if ci matches .axiomInfo _ then
      modify fun (s, a) => (s, a.push n)
    let valDeps : Array Name := match ci with
      | .thmInfo v    => v.value.getUsedConstants
      | .defnInfo v   => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | _             => #[]
    let deps := ci.type.getUsedConstants ++ valDeps
    for d in deps do
      collectAxioms env d

def main (args : List String) : IO UInt32 := do
  let [probModStr, solModStr] := args
    | IO.eprintln "usage: CheckSolution <ProblemModule> <SolutionModule>"; return 2
  let probMod := probModStr.toName
  let solMod := solModStr.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := probMod }, { module := solMod }] {} (trustLevel := 0)
  let stmt := probMod ++ `Statement
  let some stmtCi := env.find? stmt
    | IO.eprintln s!"ERROR: declaration {stmt} not found"; return 1
  unless env.getModuleIdxFor? stmt == env.getModuleIdx? probMod do
    IO.eprintln s!"ERROR: {stmt} is not declared in {probMod}"; return 1
  unless stmtCi.type == .sort .zero do
    IO.eprintln s!"ERROR: {stmt} does not have type Prop (got {stmtCi.type})"; return 1
  let expectedType (kind : String) : Expr :=
    if kind == "proof" then mkConst stmt else mkApp (mkConst ``Not) (mkConst stmt)
  let cands := ["proof", "disproof"].filterMap fun k =>
    (env.find? (solMod ++ k.toName)).map (k, ·)
  let [(kind, ci)] := cands
    | IO.eprintln s!"ERROR: expected exactly one of {solMod}.proof or {solMod}.disproof, found {cands.map (·.1)}"
      return 1
  unless ci matches .thmInfo _ | .defnInfo _ do
    IO.eprintln s!"ERROR: {ci.name} must be a theorem or definition, not an axiom/opaque"
    return 1
  unless ci.levelParams.isEmpty && ci.type == expectedType kind do
    IO.eprintln s!"ERROR: type mismatch for {ci.name}: got {ci.type}, expected {expectedType kind}"
    return 1
  unless env.getModuleIdxFor? ci.name == env.getModuleIdx? solMod do
    IO.eprintln s!"ERROR: {ci.name} is not declared in {solMod}"; return 1
  let ((), (_, axs)) := (collectAxioms env ci.name).run ({}, #[])
  let bad := axs.filter (!allowedAxioms.contains ·)
  unless bad.isEmpty do
    IO.eprintln s!"REJECTED: disallowed axioms in {ci.name}: {bad}"
    return 1
  IO.println s!"OK {kind} of {stmt}; axioms: {axs}"
  return 0
