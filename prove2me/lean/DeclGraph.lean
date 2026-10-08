import Lean

/-!
# DeclGraph: the declaration graph of a compiled development, for the carver

usage (from the prove2me workspace, after `lake build ROOT`):
  lake env lean --run DeclGraph.lean OUT.jsonl PREFIX ROOT [ROOT ...]

Imports the ROOT modules and writes OUT.jsonl, one JSON object per line:
* one per user-facing constant of a module under PREFIX (a module name prefix such as
  `Solutions.OAIErdos3`; internal auxiliaries are folded away, private names kept):
  `n` name, `m` module, `k` kind (theorem, def, axiom, opaque, inductive, ctor, rec, quot),
  `p` whether its type is a Prop (a theorem in the platform's sense), `i` whether it is an
  instance, `u` universe parameters, `s` whether its value contains `sorry`, `r` its declaration
  range `[line, col, endLine, endCol]` (null for generated constants such as `foo.proof_1`), and
  `t` / `v` the project constants its type / value use, traversing internal auxiliaries.
* one per module under PREFIX: `module`, `imports` (every direct import, project or not).
* one last line, `ext_namespaces`: the namespaces that are proper prefixes of constants from
  outside PREFIX (Mathlib, core, published bundles) and end in the same component as some project
  namespace (the only ones an `open` of a project namespace could also mean). The carver needs it to tell whether `open X`
  still names something once the project's own `X` is carved away (Erdős 3 B007: "unknown
  namespace `_root_.OAI.Set`").

Derived from the five split variants' DeclGraph.lean / deps.lean / DDGraph.lean (2026-10-07/08),
which hard-coded their root, prefix and output path. scripts/carve.py runs it.
-/

open Lean

def kindStr : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def valueConsts : ConstantInfo → Array Name
  | .thmInfo t => t.value.getUsedConstants
  | .defnInfo d => d.value.getUsedConstants
  | .opaqueInfo o => o.value.getUsedConstants
  | .inductInfo i => i.ctors.toArray
  | _ => #[]

unsafe def main (args : List String) : IO UInt32 := do
  let out :: pfx :: roots@(_ :: _) := args
    | IO.eprintln "usage: DeclGraph OUT.jsonl PREFIX ROOT [ROOT ...]"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (roots.map fun r => ({ module := r.toName } : Import)).toArray {}
    (loadExts := true)
  let projPrefix := pfx.toName
  let modNames := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).bind (modNames[·.toNat]?)
  let isProjMod (m : Name) : Bool := projPrefix.isPrefixOf m
  let isProj (n : Name) : Bool := (modOf n).any isProjMod
  let keep (n : Name) : Bool := !n.isInternal || (privateToUserName? n).isSome
  let ctx : Core.Context := { fileName := "<DeclGraph>", fileMap := default, maxHeartbeats := 0 }
  let runMeta {α : Type} (x : MetaM α) (dflt : α) : IO α := do
    match ← ((Meta.MetaM.run' x).run' ctx { env }).toBaseIO with
    | .ok a => pure a
    | .error _ => pure dflt
  -- the project constants `seed` reaches, entering internal auxiliaries
  let collect (self : Name) (seed : Array Name) : Array Name := Id.run do
    let mut acc : NameSet := {}
    let mut visited : NameSet := {}
    let mut work := seed.toList
    while h : work ≠ [] do
      let u := work.head h
      work := work.tail
      if u == self || visited.contains u then continue
      visited := visited.insert u
      unless isProj u do continue
      if keep u then acc := acc.insert u
      else if let some ci := env.find? u then
        work := (ci.type.getUsedConstants ++ valueConsts ci).toList ++ work
    return acc.toList.toArray.qsort Name.lt
  let h ← IO.FS.Handle.mk out .write
  let mut count := 0
  for (n, ci) in env.constants.toList do
    unless keep n && isProj n do continue
    let range ← runMeta (findDeclarationRanges? n) none
    let r := match range with
      | some r => toJson [r.range.pos.line, r.range.pos.column, r.range.endPos.line, r.range.endPos.column]
      | none => Json.null
    let isInst ← runMeta (Meta.isInstance n) false
    let isProp ← runMeta (Meta.isProp ci.type) false
    let hasSorry := (ci.value? (allowOpaque := true)).any (·.hasSorry)
    let j := Json.mkObj [("n", toJson n.toString), ("m", toJson ((modOf n).getD .anonymous).toString),
      ("k", toJson (kindStr ci)), ("p", toJson isProp), ("i", toJson isInst),
      ("u", toJson (ci.levelParams.map (·.toString))), ("s", toJson hasSorry), ("r", r),
      ("t", toJson ((collect n ci.type.getUsedConstants).map (·.toString))),
      ("v", toJson ((collect n (valueConsts ci)).map (·.toString)))]
    h.putStrLn j.compress
    count := count + 1
  for i in [0:modNames.size] do
    let m := modNames[i]!
    unless isProjMod m do continue
    let imps := env.header.moduleData[i]!.imports.map (·.module.toString)
    h.putStrLn (Json.mkObj [("module", toJson m.toString), ("imports", toJson imps)]).compress
  -- only the external namespaces an `open` of a project namespace could also mean: those whose
  -- last component is the last component of a project namespace (`open Aux` inside `CD` means
  -- `CD.Aux` or `Aux`); the full list is ~20k names for core alone
  let mut projLast : Std.HashSet String := {}
  for (n, _) in env.constants.toList do
    unless isProj n do continue
    let mut p := ((privateToUserName? n).getD n).getPrefix
    while !p.isAnonymous do
      projLast := projLast.insert (p.componentsRev.head!.toString)
      p := p.getPrefix
  let mut ext : NameSet := {}
  for (n, _) in env.constants.toList do
    if isProj n || n.isInternal then continue
    let mut p := n.getPrefix
    while !p.isAnonymous && !ext.contains p do
      if projLast.contains (p.componentsRev.head!.toString) then ext := ext.insert p
      p := p.getPrefix
  h.putStrLn (Json.mkObj [("ext_namespaces",
    toJson ((ext.toList.map (·.toString)).toArray.qsort (· < ·)))]).compress
  IO.eprintln s!"DeclGraph: {count} declarations"
  return 0
