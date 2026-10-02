import Lean

/-!
# LeanInfo: what a Lean file contains, as Lean itself sees it

usage (from the prove2me workspace):
  lake env lean --run LeanInfo.lean FILE.lean               -- elaborate, then report
  lake env lean --run LeanInfo.lean FILE.lean --parse-only  -- parse only (a file that does not
                                                             -- elaborate, or quick structure)

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
  (constants from our own modules -- not Mathlib or core -- with their `module`).
* `messages`: every message, with `severity`, `start`, `end` and `text`.

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
    match innerKind stx with
    | some k => [("inner_kind", toJson (toString k))]
    | none => [])

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
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let fm := inputCtx.fileMap
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- synchronous elaboration: every declaration's value is in the environment when we read it
  let opts : Options := Elab.async.set {} false
  let (env, messages) ← processHeader header opts messages inputCtx
  -- one loop for both modes, like Frontend.processCommand but keeping every message (elaboration
  -- resets the command state's log per command -- Elab/Command.lean, elabCommandTopLevel -- and
  -- each parse starts from a fresh log so its syntax errors survive too). In parse-only mode only
  -- the commands that change how later text parses or which namespace is open are elaborated
  -- (`open scoped ENNReal` makes `ℝ≥0∞` parse); declarations never are.
  let rec loop (acc : Array (Name × List OpenDecl)) (got : Array Message) :
      FrontendM (Array (Name × List OpenDecl) × Array Message) := do
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
    if !parseOnly || shapesParsing cmd.getKind then
      elabCommandAtFrontend cmd
      emsgs := (← getCommandState).messages.reportedPlusUnreported.toArray
    let got := got ++ pmsgs.toArray ++ emsgs
    if Parser.isTerminalCommand cmd then return (acc, got) else loop acc got
  let ((scopes, got), s) ← (loop #[] #[]).run { inputCtx } |>.run
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
  let mut declsJ : Array Json := #[]
  -- parse-only mode reports commands, not declarations (the few it elaborates -- notation --
  -- would make a partial, misleading list)
  for (n, ci) in (if parseOnly then [] else mine) do
    unless userFacing n do continue
    let some rg := ranges.get? n | continue
    let (used, _) := deps 64 n ∅
    let usesLocal := used.toList.filter (fun c => (env.getModuleIdxFor? c).isNone)
    let usesImported := used.toList.filterMap fun c => do
      let idx ← env.getModuleIdxFor? c
      let m := env.header.moduleNames[idx.toNat]!
      if ourModule m then some (Json.mkObj [("name", toJson (toString c)), ("module", toJson (toString m))]) else none
    let ty ← match ← ((Meta.MetaM.run' (PrettyPrinter.ppExpr ci.type)).run' { fileName := path, fileMap := fm } { env }).toBaseIO with
      | .ok f => pure (toString f)
      | .error _ => pure ""
    let user := (privateToUserName? n).getD n
    declsJ := declsJ.push <| Json.mkObj [
      ("name", toJson (toString user)), ("private", toJson (privateToUserName? n).isSome),
      ("kind", toJson (kindOf env n ci)),
      ("range", Json.mkObj [("start", positionJ fm rg.range.pos), ("end", positionJ fm rg.range.endPos)]),
      ("selection", Json.mkObj [("start", positionJ fm rg.selectionRange.pos), ("end", positionJ fm rg.selectionRange.endPos)]),
      ("type", toJson ty), ("type_hash", toJson ci.type.hash.toNat),
      ("uses_local", toJson ((usesLocal.map fun c => toString ((privateToUserName? c).getD c)).toArray.qsort (· < ·))),
      ("uses_imported", toJson usesImported.toArray)]
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
