import Lean

/-!
# EdgeUses: which of a compiled module's imports its declarations use

usage (LEAN_PATH must find MODULE's .olean and everything it imports):
  lean --run EdgeUses.lean MODULE [ROOT ...]

Loads MODULE's environment from the .olean files (no elaboration: seconds, not a compile) and
prints one JSON object: `live` and `all`, each a map from an imported module outside Mathlib and
core to the constants of it that MODULE's declarations name in their types and values (through
MODULE's own auxiliaries and declarations, never into other modules). `all` starts from every
constant of MODULE; `live` from the ROOT names (a carved piece: `solution`) and MODULE's
instances, so an import only dead code uses is in `all` but not in `live`. With no ROOT the two
agree (a bundle or statement exports everything).

What it cannot see is a use that leaves no constant behind: a `dsimp only [h]` with an rfl lemma
`h`, a notation or an `open`. p2mlib.edgecheck therefore confirms every import it calls unused by
compiling the file without it. scripts/carve_measure.py runs it (the import-edge check).
-/

open Lean

def ourModule (m : Name) : Bool :=
  !(m.getRoot ∈ [`Mathlib, `Init, `Lean, `Std, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
                 `ImportGraph, `LeanSearchClient, `Lake, `Cli])

def valueConsts : ConstantInfo → Array Name
  | .thmInfo t => t.value.getUsedConstants
  | .defnInfo d => d.value.getUsedConstants
  | .opaqueInfo o => o.value.getUsedConstants
  | .inductInfo i => i.ctors.toArray
  | _ => #[]

def toJ (m : Std.HashMap Name NameSet) : Json :=
  Json.mkObj <| m.toList.map fun (k, v) => (k.toString, toJson (v.toList.map (·.toString)))

unsafe def main (args : List String) : IO UInt32 := do
  let mod :: roots := args
    | IO.eprintln "usage: EdgeUses MODULE [ROOT ...]"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := mod.toName }] {} (loadExts := true)
  let modNames := env.header.moduleNames
  let some me := env.getModuleIdx? mod.toName
    | IO.eprintln s!"module {mod} not loaded"; return 2
  let mine : Array Name := env.header.moduleData[me.toNat]!.constNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).bind (modNames[·.toNat]?)
  let ctx : Core.Context := { fileName := "<EdgeUses>", fileMap := default, maxHeartbeats := 0 }
  let isInst (n : Name) : IO Bool := do
    match ← ((Meta.MetaM.run' (Meta.isInstance n)).run' ctx { env }).toBaseIO with
    | .ok b => pure b
    | .error _ => pure false
  -- walk from `seed` through MODULE's own constants; record what other modules supply
  let walk (seed : List Name) : Std.HashMap Name NameSet := Id.run do
    let mut out : Std.HashMap Name NameSet := {}
    let mut visited : NameSet := {}
    let mut work := seed
    while h : work ≠ [] do
      let u := work.head h
      work := work.tail
      if visited.contains u then continue
      visited := visited.insert u
      match modOf u with
      | some m =>
        if m == mod.toName then
          if let some ci := env.find? u then
            work := (ci.type.getUsedConstants ++ valueConsts ci).toList ++ work
        else if ourModule m then
          out := out.insert m ((out.getD m {}).insert u)
      | none => pure ()
    return out
  let all := walk mine.toList
  let mut seeds : List Name := roots.map (·.toName)
  if roots.isEmpty then seeds := mine.toList
  else
    for n in mine do
      if ← isInst n then seeds := n :: seeds
  let live := walk seeds
  IO.println (Json.mkObj [("live", toJ live), ("all", toJ all)]).compress
  return 0
