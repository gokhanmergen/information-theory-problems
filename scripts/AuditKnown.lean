/-
Audit for the proved-results libraries `InfoTheory.Known.*` (incl. `Known.Certificates.*`)
and `InfoTheory.Bridge.*`.

Usage (from `lean/`, after
  `lake build InfoTheory.Known InfoTheory.Known.Certificates InfoTheory.Bridge`):
  lake env lean --run ../scripts/AuditKnown.lean

Loads the compiled `.olean` environment (no user syntax is elaborated, so macros defined in
the audited files cannot influence the result) and checks:
1. Axioms: every declaration under the audited prefixes has a transitive constant closure
   (including theorem bodies) using only `propext`, `Classical.choice`, `Quot.sound`.
2. Name collisions: no `InfoTheory.Known.X` may coexist with `InfoTheory.Bridge.X`; otherwise
   any file opening both namespaces hits "ambiguous term" errors. Shared basics belong in
   `InfoTheory.Bridge`.
3. Certificate coverage (informational): which `InfoTheory.Problems.<M>` statements have a
   certificate module `InfoTheory.Known.Certificates.<M>` proving their docstring's known facts.
Kernel re-checking is done separately with `lake env leanchecker <Module>`.
-/
import Lean
open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def roots : Array Name :=
  #[`InfoTheory.Known, `InfoTheory.Known.Certificates, `InfoTheory.Bridge, `InfoTheory.Problems]
def auditedPrefixes : List Name := [`InfoTheory.Known, `InfoTheory.Bridge]

partial def collect (env : Environment) (n : Name) : StateM (NameSet × Array Name) Unit := do
  let (seen, _) ← get
  if seen.contains n then return
  modify fun (s, a) => (s.insert n, a)
  match env.find? n with
  | none => modify fun (s, a) => (s, a.push (`__missing__ ++ n))
  | some ci =>
    if ci matches .axiomInfo _ then modify fun (s, a) => (s, a.push n)
    let deps := ci.type.getUsedConstants ++ (match ci with
      | .thmInfo v => v.value.getUsedConstants
      | .defnInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | _ => #[])
    for d in deps do collect env d

/-- User-facing declaration (not private, not compiler/elaborator-generated). -/
def isUserDecl (n : Name) : Bool :=
  !isPrivateName n && !n.isInternalDetail &&
    !(n.components.any fun c => c.toString.startsWith "eq_" || c.toString.startsWith "match_" ||
      c.toString.startsWith "proof_" || c == `_cstage1 || c == `_cstage2)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (roots.map ({ module := · })) {} (trustLevel := 0)
  let modName (n : Name) : Option Name := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
  let audited (m : Name) : Bool := auditedPrefixes.any (·.isPrefixOf m)
  let mods := env.header.moduleNames.filter audited
  let mut nThm := 0
  let mut nBad := 0
  let mut collisions : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    let some m := modName n | continue
    unless audited m do continue
    if ci matches .thmInfo _ then nThm := nThm + 1
    -- 1. axioms
    let ((), (_, axs)) := (collect env n).run ({}, #[])
    let bad := axs.filter (!allowed.contains ·)
    unless bad.isEmpty do
      nBad := nBad + 1
      IO.println s!"BAD AXIOMS {n}: {bad}"
    -- 2. Known/Bridge name collisions
    if (`InfoTheory.Known).isPrefixOf n && isUserDecl n then
      let twin := n.replacePrefix `InfoTheory.Known `InfoTheory.Bridge
      if env.contains twin then collisions := collisions.push (n, twin)
  for (a, b) in collisions do
    IO.println s!"NAME COLLISION {a} vs {b}: delete the Known copy and import the Bridge one"
  -- 3. certificate coverage
  let problemMods := env.header.moduleNames.filter fun m =>
    (`InfoTheory.Problems).isPrefixOf m && m.getNumParts == 3
  let certified := problemMods.filter fun m =>
    env.header.moduleNames.contains (`InfoTheory.Known.Certificates ++ m.componentsRev.head!)
  IO.println s!"modules audited: {mods.size}"
  IO.println s!"audited {nThm} theorems; disallowed-axiom declarations: {nBad}; name collisions: {collisions.size}"
  IO.println s!"certificate coverage: {certified.size}/{problemMods.size} problem statements"
  IO.println s!"certified: {certified.map (·.componentsRev.head!)}"
  return (if nBad == 0 && collisions.isEmpty then 0 else 1)
