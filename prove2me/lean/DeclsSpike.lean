import Lean
open Lean Elab Frontend

unsafe def main (args : List String) : IO Unit := do
  let path := args.head!
  let input ← IO.FS.readFile path
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  IO.println s!"after header: {env.contains `Nat.add} natadd, {messages.toList.length} msgs, header imports {(env.header.moduleNames.size)}"
  for m in messages.toList do IO.println s!"HMSG {← m.toString}"
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  let env := s.commandState.env
  let fm := inputCtx.fileMap
  for cmd in s.commands do
    if let some r := cmd.getRange? then
      IO.println s!"CMD {cmd.getKind} {(fm.toPosition r.start).line}-{(fm.toPosition r.stop).line}"
  for m in s.commandState.messages.toList do
    IO.println s!"MSG {← m.toString}"
  IO.println s!"contains Foo.bar': {env.contains `Foo.bar'}  solution: {env.contains `solution}"
  let mine := env.constants.toList.filter (fun (n, _) => (env.getModuleIdxFor? n).isNone && !n.isInternal)
  for (n, ci) in mine do
    let res ← ((findDeclarationRanges? n : CoreM _).run' {fileName := path, fileMap := fm} {env}).toBaseIO
    match res with
    | .ok (some rg) =>
      let used := ci.getUsedConstantsAsSet.toList.filter (fun c => (env.getModuleIdxFor? c).isNone || c.toString.startsWith "Foo")
      IO.println s!"DECL {n} lines {rg.range.pos.line}-{rg.range.endPos.line} uses {used}"
    | _ => pure ()
