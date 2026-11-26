/-
Axiom audit for the proved-results libraries `InfoTheory.Known.*` and `InfoTheory.Bridge.*`.

Usage (from `lean/`, after `lake build InfoTheory.Known InfoTheory.Bridge.Mathlib`):
  lake env lean --run ../scripts/AuditKnown.lean

Loads the compiled `.olean` environment (no user syntax is elaborated, so macros defined in
the audited files cannot influence the result). Every declaration whose module lies under one
of the audited prefixes is checked: its transitive constant closure, including theorem bodies,
may use only `propext`, `Classical.choice`, `Quot.sound`. New files under those prefixes are
picked up automatically once imported by `InfoTheory.Known` / the Bridge.
Kernel re-checking is done separately with `lake env leanchecker <Module>`.
-/
import Lean
open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def roots : Array Name := #[`InfoTheory.Known, `InfoTheory.Bridge.Mathlib]
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

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (roots.map ({ module := · })) {} (trustLevel := 0)
  let audited (m : Name) : Bool := auditedPrefixes.any (·.isPrefixOf m)
  let mods := env.header.moduleNames.filter audited
  let mut nThm := 0
  let mut nBad := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless audited env.header.moduleNames[idx.toNat]! do continue
    if ci matches .thmInfo _ then nThm := nThm + 1
    let ((), (_, axs)) := (collect env n).run ({}, #[])
    let bad := axs.filter (!allowed.contains ·)
    unless bad.isEmpty do
      nBad := nBad + 1
      IO.println s!"BAD {n}: {bad}"
  IO.println s!"modules: {mods}"
  IO.println s!"audited {nThm} theorems; declarations with disallowed axioms: {nBad}"
  return (if nBad == 0 then 0 else 1)
