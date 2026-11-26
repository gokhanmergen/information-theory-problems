/- Audit every declaration in InfoTheory.Known.* for non-standard axioms (loads compiled
   .oleans; no user syntax is elaborated). Run from lean/: lake env lean --run ../scripts/AuditKnown.lean -/
import Lean
open Lean
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
partial def collect (env : Environment) (n : Name) : StateM (NameSet × Array Name) Unit := do
  let (seen, _) ← get
  if seen.contains n then return
  modify fun (s, a) => (s.insert n, a)
  match env.find? n with
  | none => modify fun (s, a) => (s, a.push (`__missing__ ++ n))
  | some ci =>
    if ci matches .axiomInfo _ then modify fun (s, a) => (s, a.push n)
    let deps := ci.type.getUsedConstants ++ (match ci with
      | .thmInfo v => v.value.getUsedConstants | .defnInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants | _ => #[])
    for d in deps do collect env d
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods := #[`InfoTheory.Known.Entropy, `InfoTheory.Known.EntropyRegion, `InfoTheory.Known.Channels,
                `InfoTheory.Known.Coding, `InfoTheory.Known.ZeroError]
  let env ← importModules (mods.map ({ module := · })) {} (trustLevel := 0)
  let mut nThm := 0; let mut nBad := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless mods.contains (env.header.moduleNames[idx.toNat]!) do continue
    if ci matches .thmInfo _ then nThm := nThm + 1
    let ((), (_, axs)) := (collect env n).run ({}, #[])
    let bad := axs.filter (!allowed.contains ·)
    unless bad.isEmpty do nBad := nBad + 1; IO.println s!"BAD {n}: {bad}"
  IO.println s!"audited {nThm} theorems across Known/*; declarations with disallowed axioms: {nBad}"
  return (if nBad == 0 then 0 else 1)
