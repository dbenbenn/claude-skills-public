import Lean

/-!
# DeclGraph: the declaration graph of a compiled development, for the carver

usage (from the prove2me workspace, after `lake build ROOT`):
  lake env lean --run DeclGraph.lean [--also MODULE ...] OUT.jsonl PREFIX ROOT [ROOT ...]

`--also MODULE` treats that module as part of the project although it is outside PREFIX: the
Theorems module of someone else's published theorem the development imports (carve.py
`external_theorems`), so its constant is a node and its users' edges are recorded.

Imports the ROOT modules and writes OUT.jsonl, one JSON object per line:
* one per user-facing constant of a module under PREFIX (a module name prefix such as
  `Solutions.OAIErdos3`; internal auxiliaries are folded away, private names kept):
  `n` name, `m` module, `k` kind (theorem, def, axiom, opaque, inductive, ctor, rec, quot),
  `p` whether its type is a Prop (a theorem in the platform's sense), `i` whether it is an
  instance, `u` universe parameters, `s` whether its value contains `sorry`, `r` its declaration
  range `[line, col, endLine, endCol]` (null for generated constants such as `foo.proof_1`), and
  `t` / `v` the project constants its type / value use, traversing internal auxiliaries; for a
  theorem whose type has universe parameters occurring in it only under `max`/`imax` (never bare,
  as `u` or `u+1`), `mu` lists them (the verifier's statement check can get "stuck at solving
  universe constraint `max ?a ?v =?= max ?b ?v`" on such a type, oaiq-124).
* `"dup": true` records: a theorem declared under the same full name by two modules, which Lean
  imports together when their types agree (`subsumesInfo`), so the environment keeps one copy
  and names the first module imported; the main record above is that module's own copy, and each
  other module's copy gets a record of its own (`m` that module, `t` / `v` from its own value,
  `r` null). The carver renames all but one copy (oaiq-088/090/095/096: a piece holding two
  modules' copies used the one declared later, "Unknown identifier").
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

/-- The universe parameters a level mentions bare (`u`, `u+1`) / at all. -/
def bareParams : Level → NameSet → NameSet
  | .param n, s => s.insert n
  | .succ l, s => bareParams l s
  | _, s => s

def allParams : Level → NameSet → NameSet
  | .param n, s => s.insert n
  | .succ l, s => allParams l s
  | .max a b, s | .imax a b, s => allParams b (allParams a s)
  | _, s => s

/-- The universe parameters occurring in `e`'s levels bare and at all, each shared subterm once. -/
unsafe def univOcc (e : Expr) (acc : PtrSet Expr × NameSet × NameSet) : PtrSet Expr × NameSet × NameSet :=
  if acc.1.contains e then acc else
  let acc := (acc.1.insert e, acc.2)
  let lv (l : Level) (a : PtrSet Expr × NameSet × NameSet) := (a.1, bareParams l a.2.1, allParams l a.2.2)
  match e with
  | .sort l => lv l acc
  | .const _ ls => ls.foldl (fun a l => lv l a) acc
  | .app f a => univOcc a (univOcc f acc)
  | .lam _ t b _ | .forallE _ t b _ => univOcc b (univOcc t acc)
  | .letE _ t v b _ => univOcc b (univOcc v (univOcc t acc))
  | .mdata _ b | .proj _ _ b => univOcc b acc
  | _ => acc

/-- The universe parameters of `ty` occurring in it only under `max`/`imax`. -/
unsafe def maxOnlyUniverses (ty : Expr) : Array Name :=
  let (_, bare, all) := univOcc ty (mkPtrSet, {}, {})
  (all.toList.filter (!bare.contains ·)).toArray.qsort Name.lt

/-- Leading `--also MODULE` pairs, and the remaining arguments. -/
def splitAlso : List String → List Name × List String
  | "--also" :: m :: rest => let (ms, r) := splitAlso rest; (m.toName :: ms, r)
  | rest => ([], rest)

unsafe def main (args0 : List String) : IO UInt32 := do
  let (also, args) := splitAlso args0
  let out :: pfx :: roots@(_ :: _) := args
    | IO.eprintln "usage: DeclGraph [--also MODULE ...] OUT.jsonl PREFIX ROOT [ROOT ...]"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (roots.map fun r => ({ module := r.toName } : Import)).toArray {}
    (loadExts := true)
  let projPrefix := pfx.toName
  let modNames := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).bind (modNames[·.toNat]?)
  let isProjMod (m : Name) : Bool := projPrefix.isPrefixOf m || also.contains m
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
  -- a theorem two project modules declare (imported together: their types agree): each module's
  -- own copy, the environment's module (`modOf`) included, whose copy the environment may have
  -- replaced by a later module's
  let mut dups : Array (Name × ConstantInfo) := #[]
  let mut own : Std.HashMap Name ConstantInfo := {}
  for i in [0:modNames.size] do
    unless isProjMod modNames[i]! do continue
    for ci in env.header.moduleData[i]!.constants do
      if keep ci.name && (env.getModuleIdxFor? ci.name).any (·.toNat != i) then
        dups := dups.push (modNames[i]!, ci)
  for (_, ci) in dups do
    unless own.contains ci.name do
      if let some idx := env.getModuleIdxFor? ci.name then
        if let some c := env.header.moduleData[idx.toNat]!.constants.find? (·.name == ci.name) then
          own := own.insert ci.name c
  let record (n m : Name) (ci : ConstantInfo) (r : Json) (dup : Bool) : IO Json := do
    let isInst ← runMeta (Meta.isInstance n) false
    let isProp ← runMeta (Meta.isProp ci.type) false
    let hasSorry := (ci.value? (allowOpaque := true)).any (·.hasSorry)
    let mu := if ci matches .thmInfo _ then maxOnlyUniverses ci.type else #[]
    return Json.mkObj <| [("n", toJson n.toString), ("m", toJson m.toString),
      ("k", toJson (kindStr ci)), ("p", toJson isProp), ("i", toJson isInst),
      ("u", toJson (ci.levelParams.map (·.toString))), ("s", toJson hasSorry), ("r", r),
      ("t", toJson ((collect n ci.type.getUsedConstants).map (·.toString))),
      ("v", toJson ((collect n (valueConsts ci)).map (·.toString)))] ++
      (if mu.isEmpty then [] else [("mu", toJson (mu.map (·.toString)))]) ++
      (if dup then [("dup", toJson true)] else [])
  let h ← IO.FS.Handle.mk out .write
  let mut count := 0
  for (n, ci) in env.constants.toList do
    unless keep n && isProj n do continue
    let range ← runMeta (findDeclarationRanges? n) none
    let r := match range with
      | some r => toJson [r.range.pos.line, r.range.pos.column, r.range.endPos.line, r.range.endPos.column]
      | none => Json.null
    h.putStrLn (← record n ((modOf n).getD .anonymous) (own.getD n ci) r false).compress
    count := count + 1
  for (m, ci) in dups do
    h.putStrLn (← record ci.name m ci Json.null true).compress
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
