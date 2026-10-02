import Lean

/-!
# LeanInfo: what a Lean file contains, as Lean itself sees it

usage (from the prove2me workspace):
  lake env lean --run LeanInfo.lean FILE.lean               -- elaborate, then report
  lake env lean --run LeanInfo.lean FILE.lean --parse-only  -- parse only (a file that does not
                                                             -- elaborate, or quick structure)
  lake env lean --run LeanInfo.lean FILE.lean --candidates M1,M2,...
                                                             -- also import these modules and
                                                             -- report copies of their theorems

Prints one JSON object:
* `commands`: every command in order, with `kind` (the syntax kind), `start`/`end` positions
  (`line`, `col`, `byte`), the `namespace` and `opens` in force before it, for an `open … in` its
  `inner_kind`, the `attrs` written on it, and the `name`s it declares (from syntax: available in
  both modes).
* `decls` (elaborate mode): every declaration of this file that a user wrote (auxiliary constants
  are folded away), with its full `name`, `private`, `kind`, `range` and `selection` (positions as
  above; `range` includes the doc comment and modifiers), `type` (pretty-printed), `type_hash` (the
  type's `Expr.hash`: equal for statements differing only in binder names or binder brackets;
  NOT equal when one hides its statement behind a local definition -- that needs a defeq check), and
  `uses_local` (declarations of this file it depends on, through auxiliaries) and `uses_imported`
  (constants from our own modules -- not Mathlib or core -- with their `module`). A dependency is a
  constant in the declaration's value OR one its command names in source (every constant the
  elaborator resolved there, from the info trees): `simp only [h]` with an `rfl` lemma `h` rewrites
  by `dsimp` and leaves no trace in the term, yet deleting `h` breaks the proof. A name tried in a
  failed `first` alternative counts too, so the lists can over-approximate; never under.
* `messages`: every message, with `severity`, `start`, `end` and `text`.
* with `--candidates`: each theorem of the file has `same_statement_as`, the candidate modules'
  theorems that state the same thing. Two statements are the same when they are equal after
  renaming universe parameters by position, unfolding this file's Prop-valued definitions (a
  local predicate such as `CommonCaret` standing for a published clause), and replacing every
  proof inside them by one constant (`get ⟨i, by omega⟩` elaborates to different proof terms in
  different files); `Expr` equality already ignores binder names and binder brackets. Deliberately
  NOT up to definitional unfolding in general: `isDefEq` would equate `2 + 2 = 4` with `4 = 2 + 2`
  and invent a dependency. The candidate modules are imported beside the file's own, so a file
  declaring a candidate's full name fails to elaborate: leave such a module out.

In parse-only mode the commands that change how later text parses (`namespace`, `section`, `end`,
`open`, `set_option`, `universe`, notation, `syntax`, `macro`) are still elaborated, so scoped
and in-file notation parse; declarations are not, and `decls` is empty.

The prove2me scripts ask this instead of matching Lean with regular expressions
(scripts/ENGINEERING_PLAN.md, Phase 2).
-/

open Lean Elab Frontend

namespace LeanInfo

/-- `""` for the root namespace (Lean prints it `[anonymous]`). -/
def nsStr (n : Name) : String := if n.isAnonymous then "" else toString n

def posJ (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let q := fm.toPosition p
  Json.mkObj [("line", q.line), ("col", q.column), ("byte", p.byteIdx)]

def positionJ (fm : FileMap) (q : Position) : Json :=
  Json.mkObj [("line", q.line), ("col", q.column), ("byte", (fm.ofPosition q).byteIdx)]

def openJ : OpenDecl → Json
  | .simple ns ex => Json.mkObj [("namespace", toJson (nsStr ns)), ("except", toJson (ex.map toString))]
  | .explicit id d => Json.mkObj [("id", toJson (toString id)), ("decl", toJson (toString d))]

/-- Every constant the elaborator resolved in these info trees (identifiers, `simp` lemma lists,
`unfold` targets, the heads of elaborated applications). -/
def referencedConsts (trees : Array InfoTree) : NameSet :=
  trees.foldl (init := ∅) fun acc t => t.foldInfo (init := acc) fun _ i acc =>
    match i with
    | .ofTermInfo ti => match ti.expr.getAppFn with
      | .const n _ => acc.insert n
      | _ => acc
    | _ => acc

/-- A statement as compared for copies (see the module doc): universes renamed by position, this
file's predicates unfolded, proofs erased. -/
def normStatement (isLocalPred : Name → Bool) (ci : ConstantInfo) : MetaM Expr := do
  let us := (List.range ci.levelParams.length).map fun i => mkLevelParam (.mkSimple s!"u{i}")
  let ty ← Meta.deltaExpand (ci.type.instantiateLevelParams ci.levelParams us) isLocalPred
  Meta.transform ty (pre := fun e => do
    if e.isSort || e.isConst || e.isLit then return .continue
    try
      if ← Meta.isProof e then return .done (mkConst `LeanInfo.proof) else return .continue
    catch _ => return .continue)

/-- Names declared by a command, from its syntax: every `declId` (and the `in`-wrapped command's). -/
partial def declaredNames (ns : Name) (stx : Syntax) : Array String := Id.run do
  let mut out := #[]
  if stx.getKind == ``Lean.Parser.Command.declId then
    let id := stx[0].getId
    let full := if id.getRoot == `_root_ then id.replacePrefix `_root_ Name.anonymous else ns ++ id
    return #[toString full]
  for a in stx.getArgs do
    out := out ++ declaredNames ns a
  return out

/-- Attribute names written on a command (`@[simp, instance]`), from its syntax. -/
partial def attrNames (stx : Syntax) : Array String := Id.run do
  let mut out := #[]
  if stx.getKind == ``Lean.Parser.Term.attrInstance then
    let txt := (stx.reprint.getD "").trimAscii.toString
    return #[txt]
  for a in stx.getArgs do
    out := out ++ attrNames a
  return out

/-- For a declaration command (possibly wrapped in `open … in` / `set_option … in`, nested): the
kind of the declaration itself -- `theorem`, `definition`, `instance`, `structure`, `inductive`, …
Mathlib's `lemma` is a command of its own (Mathlib/Tactic/Lemma.lean) that elaborates as a
`theorem`, and is reported as one: without this every `lemma` looked like a non-declaration and the
pruner could never delete one (71 of them in a Moore solution, 2026-10-02). -/
partial def declKind (stx : Syntax) : Option Name :=
  if stx.getKind == ``Lean.Parser.Command.in then declKind stx[2]
  else if stx.getKind == ``Lean.Parser.Command.declaration then some stx[1].getKind
  else if stx.getKind == `lemma then some ``Lean.Parser.Command.theorem
  else none

def innerKind (stx : Syntax) : Option Name :=
  if stx.getKind == ``Lean.Parser.Command.in then some stx[2].getKind else none

def commandJ (fm : FileMap) (stx : Syntax) (scope : Name × List OpenDecl) : Option Json := do
  let r ← stx.getRange?
  let (ns, opens) := scope
  some <| Json.mkObj ([
    ("kind", toJson (toString stx.getKind)),
    ("start", posJ fm r.start), ("end", posJ fm r.stop),
    ("namespace", toJson (nsStr ns)),
    ("opens", toJson (opens.map openJ)),
    ("attrs", toJson (attrNames stx)),
    ("names", toJson (declaredNames ns stx))] ++
    (match innerKind stx with
    | some k => [("inner_kind", toJson (toString k))]
    | none => []) ++
    (match declKind stx with
    | some k => [("decl_kind", toJson (toString k))]
    | none => []))

/-- Commands elaborated even in parse-only mode: they change how later text parses (notation,
syntax, scoped opens) or which namespace and options are in force. Declarations are not. -/
def shapesParsing (k : Name) : Bool :=
  k ∈ [`Lean.Parser.Command.namespace, `Lean.Parser.Command.section, `Lean.Parser.Command.end,
       `Lean.Parser.Command.open, `Lean.Parser.Command.set_option, `Lean.Parser.Command.universe,
       `Lean.Parser.Command.noncomputableSection, `Lean.Parser.Command.notation,
       `Lean.Parser.Command.mixfix, `Lean.Parser.Command.macro, `Lean.Parser.Command.syntax,
       `Lean.Parser.Command.macro_rules, `Lean.Parser.Command.syntaxAbbrev,
       `Lean.Parser.Command.syntaxCat] ||
  (k.toString.endsWith "notation3")

def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => if isStructure env n then "structure" else "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => if isStructure env n then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def ourModule (m : Name) : Bool :=
  !(m.getRoot ∈ [`Mathlib, `Init, `Lean, `Std, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
                 `ImportGraph, `LeanSearchClient, `Lake, `Cli])

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: LeanInfo FILE.lean [--parse-only]"; return 2
  let parseOnly := args.contains "--parse-only"
  let candidates : Array Name := match args.dropWhile (· != "--candidates") with
    | _ :: ms :: _ => (ms.splitOn ",").filter (· ≠ "") |>.map String.toName |>.toArray
    | _ => #[]
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let fm := inputCtx.fileMap
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- synchronous elaboration: every declaration's value is in the environment when we read it
  let opts : Options := Elab.async.set {} false
  let (env, messages) ← processHeaderCore (HeaderSyntax.startPos header)
    (HeaderSyntax.imports header ++ candidates.map fun m => ({ module := m } : Import))
    (HeaderSyntax.isModule header)
    opts messages inputCtx (headerStx? := header)
  -- one loop for both modes, like Frontend.processCommand but keeping every message (elaboration
  -- resets the command state's log per command -- Elab/Command.lean, elabCommandTopLevel -- and
  -- each parse starts from a fresh log so its syntax errors survive too). In parse-only mode only
  -- the commands that change how later text parses or which namespace is open are elaborated
  -- (`open scoped ENNReal` makes `ℝ≥0∞` parse); declarations never are.
  let rec loop (acc : Array (Name × List OpenDecl)) (got : Array Message) (refs : Array NameSet) :
      FrontendM (Array (Name × List OpenDecl) × Array Message × Array NameSet) := do
    updateCmdPos
    let cmdState ← getCommandState
    let scope := cmdState.scopes.head!
    let acc := acc.push (scope.currNamespace, scope.openDecls)
    let pmctx : Parser.ParserModuleContext :=
      { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps, pmsgs) := Parser.parseCommand (← getInputContext) pmctx (← getParserState) {}
    modify fun st => { st with commands := st.commands.push cmd }
    setParserState ps
    let mut emsgs : Array Message := #[]
    let mut cmdRefs : NameSet := ∅
    if !parseOnly || shapesParsing cmd.getKind then
      elabCommandAtFrontend cmd
      emsgs := (← getCommandState).messages.reportedPlusUnreported.toArray
      unless parseOnly do
        -- the info state, like the message log, is per command (elabCommandTopLevel resets both),
        -- so every tree in it is this command's; fill their holes before reading them
        let info ← IO.wait (← getCommandState).infoState.substituteLazy
        cmdRefs := referencedConsts (info.trees.toArray.map (·.substitute info.assignment))
    let got := got ++ pmsgs.toArray ++ emsgs
    let refs := refs.push cmdRefs
    if Parser.isTerminalCommand cmd then return (acc, got, refs) else loop acc got refs
  let ((scopes, got, cmdRefs), s) ← (loop #[] #[] #[]).run { inputCtx } |>.run
    { commandState := Command.mkState env {} opts, parserState, cmdPos := parserState.pos }
  let cmds := s.commands.zip scopes
  let msgArr := messages.reportedPlusUnreported.toArray ++ got
  let finalEnv := s.commandState.env
  let env := finalEnv
  let commandsJ := cmds.filterMap fun (stx, sc) => commandJ fm stx sc
  -- declarations: user-facing constants of this file (they have declaration ranges)
  let mine := env.constants.toList.filter fun (n, _) => (env.getModuleIdxFor? n).isNone
  let mut ranges : Std.HashMap Name DeclarationRanges := {}
  for (n, _) in mine do
    if let .ok (some rg) ← ((findDeclarationRanges? n : CoreM _).run' { fileName := path, fileMap := fm } { env }).toBaseIO then
      ranges := ranges.insert n rg
  let userFacing (n : Name) : Bool :=
    ranges.contains n && !(n.isInternal && (privateToUserName? n).isNone)
  -- dependencies, folded through auxiliary constants of this file
  let rec deps (fuel : Nat) (n : Name) (seen : NameSet) : NameSet × NameSet := Id.run do
    let some ci := env.find? n | return (∅, seen)
    let mut out : NameSet := ∅
    let mut seen := seen
    if fuel = 0 then return (out, seen)
    for c in ci.getUsedConstantsAsSet.toList do
      if seen.contains c || c == n then continue
      seen := seen.insert c
      if (env.getModuleIdxFor? c).isSome || userFacing c then
        out := out.insert c
      else
        let (o, s') := deps (fuel - 1) c seen
        out := out.union o; seen := s'
    return (out, seen)
  -- the command each declaration came from: the last one starting at or before its range
  let cmdStarts : Array Nat := s.commands.map fun stx => (stx.getPos?.getD 0).byteIdx
  let refsOf (rg : DeclarationRanges) : NameSet := Id.run do
    let b := (fm.ofPosition rg.range.pos).byteIdx
    let mut out : NameSet := ∅
    for i in [0:cmdStarts.size] do
      if cmdStarts[i]! ≤ b then out := cmdRefs.getD i ∅
    return out
  -- copies (--candidates): the candidate modules' theorems, indexed by normalised statement
  let candSet : NameSet := candidates.foldl (·.insert ·) ∅
  let isLocalPred (c : Name) : Bool := (env.getModuleIdxFor? c).isNone &&
    match env.find? c with
    | some (.defnInfo d) => d.type.getForallBody.isProp
    | _ => false
  let runMeta {α : Type} (x : MetaM α) : IO (Option α) := do
    match ← ((Meta.MetaM.run' x).run' { fileName := path, fileMap := fm } { env }).toBaseIO with
    | .ok a => pure (some a)
    | .error _ => pure none
  let mut index : Std.HashMap UInt64 (Array (Name × Expr)) := {}
  if !parseOnly && !candidates.isEmpty then
    for (n, ci) in env.constants.toList do
      let some idx := env.getModuleIdxFor? n | continue
      unless candSet.contains env.header.moduleNames[idx.toNat]! do continue
      unless (match ci with | .thmInfo _ => true | _ => false) && !n.isInternal do continue
      if let some e ← runMeta (normStatement isLocalPred ci) then
        index := index.insert e.hash ((index.getD e.hash #[]).push (n, e))
  let mut declsJ : Array Json := #[]
  -- parse-only mode reports commands, not declarations (the few it elaborates -- notation --
  -- would make a partial, misleading list)
  for (n, ci) in (if parseOnly then [] else mine) do
    unless userFacing n do continue
    let some rg := ranges.get? n | continue
    let (used, _) := deps 64 n ∅
    -- plus what the source names: an imported or user-facing name as is, an auxiliary folded
    let mut used := used
    for c in (refsOf rg).toList do
      if c == n || used.contains c then continue
      if (env.getModuleIdxFor? c).isSome || userFacing c then used := used.insert c
      else if (env.find? c).isSome then used := used.union (deps 64 c ∅).1
    let usesLocal := used.toList.filter (fun c => (env.getModuleIdxFor? c).isNone)
    let usesImported := used.toList.filterMap fun c => do
      let idx ← env.getModuleIdxFor? c
      let m := env.header.moduleNames[idx.toNat]!
      if ourModule m then some (Json.mkObj [("name", toJson (toString c)), ("module", toJson (toString m))]) else none
    let ty ← match ← ((Meta.MetaM.run' (PrettyPrinter.ppExpr ci.type)).run' { fileName := path, fileMap := fm } { env }).toBaseIO with
      | .ok f => pure (toString f)
      | .error _ => pure ""
    let user := (privateToUserName? n).getD n
    let mut same : Array String := #[]
    if !candidates.isEmpty && (match ci with | .thmInfo _ => true | _ => false) then
      if let some e ← runMeta (normStatement isLocalPred ci) then
        same := (index.getD e.hash #[]).filterMap fun (m, e') =>
          if m != n && e' == e then some (toString m) else none
    declsJ := declsJ.push <| Json.mkObj [
      ("name", toJson (toString user)), ("private", toJson (privateToUserName? n).isSome),
      ("kind", toJson (kindOf env n ci)),
      ("range", Json.mkObj [("start", positionJ fm rg.range.pos), ("end", positionJ fm rg.range.endPos)]),
      ("selection", Json.mkObj [("start", positionJ fm rg.selectionRange.pos), ("end", positionJ fm rg.selectionRange.endPos)]),
      ("type", toJson ty), ("type_hash", toJson ci.type.hash.toNat),
      ("uses_local", toJson ((usesLocal.map fun c => toString ((privateToUserName? c).getD c)).toArray.qsort (· < ·))),
      ("uses_imported", toJson usesImported.toArray)] |>.mergeObj
      (if candidates.isEmpty then Json.mkObj [] else Json.mkObj [("same_statement_as", toJson same)])
  let declsSorted := declsJ.qsort fun a b =>
    (a.getObjValD "range" |>.getObjValD "start" |>.getObjValD "byte" |>.getNat?.toOption.getD 0) <
    (b.getObjValD "range" |>.getObjValD "start" |>.getObjValD "byte" |>.getNat?.toOption.getD 0)
  let mut msgsJ : Array Json := #[]
  for m in msgArr do
    let sev := match m.severity with | .error => "error" | .warning => "warning" | .information => "information"
    msgsJ := msgsJ.push <| Json.mkObj [
      ("severity", toJson sev), ("start", positionJ fm m.pos), ("end", positionJ fm (m.endPos.getD m.pos)),
      ("text", toJson (← m.data.toString))]
  IO.println <| Json.compress <| Json.mkObj [
    ("file", toJson path), ("mode", toJson (if parseOnly then "parse" else "elaborate")),
    ("commands", toJson commandsJ), ("decls", toJson declsSorted), ("messages", toJson msgsJ)]
  return 0

end LeanInfo

unsafe def main (args : List String) : IO UInt32 := LeanInfo.main args
