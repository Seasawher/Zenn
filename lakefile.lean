import Lake

open System Lake DSL

package Articles where

@[default_target]
lean_lib Article where
  globs := #[.submodules `Article]

require "Seasawher" / "mdgen" @ git "main"
require "leanprover-community" / "batteries" @ git "main"

def runCmdWithOutput (input : String) (stdIn : Option String := none) : IO String := do
  let cmdList := input.splitOn " "
  let cmd := cmdList.head!
  let args := cmdList.tail |>.toArray
  let out ← IO.Process.output
    (args := {cmd := cmd, args := args})
    (input? := stdIn)
  unless out.exitCode == 0 do
    IO.eprintln out.stderr
    throw <| IO.userError s!"Failed to execute: {input}"

  return out.stdout.trimAscii.copy

def runCmd (input : String) : IO Unit := do
  let out ← runCmdWithOutput input
  if out != "" then
    IO.println out

script "build" do
  runCmd "lake exe mdgen Article articles"
  return 0
