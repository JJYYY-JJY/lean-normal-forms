/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

/-!
# Repository lint driver

This lightweight Lake lint target checks source trust markers, facade import
hygiene, whitespace, and the import graph without changing files.
-/

private def printFailure (description : String) (result : IO.Process.Output) : IO Unit := do
  IO.eprintln description
  unless result.stdout.isEmpty do
    IO.eprint result.stdout
  unless result.stderr.isEmpty do
    IO.eprint result.stderr

private def requireSuccess (description command : String) (arguments : Array String) : IO Bool := do
  let result ← IO.Process.output { cmd := command, args := arguments }
  if result.exitCode == 0 then
    return true
  printFailure description result
  return false

private def requireNoMatches
    (description pattern : String) (extraArguments paths : Array String) : IO Bool := do
  let result ← IO.Process.output
    { cmd := "rg", args := #["-n"] ++ extraArguments ++ #["--", pattern] ++ paths }
  if result.exitCode == 1 then
    return true
  if result.exitCode == 0 then
    printFailure description result
  else
    printFailure s!"{description} (rg failed)" result
  return false

private def checkImports : IO Bool := do
  let result ← IO.Process.output
    { cmd := "lake", args := #["shake", "--keep-public", "NormalForms"] }
  let suggestions := (result.stdout.splitOn "remove #[").length - 1
  let analyzed :=
    result.exitCode == 0 ||
      (result.exitCode == 1 && result.stderr.isEmpty && suggestions > 0)
  if !analyzed then
    printFailure "import graph analysis failed" result
    return false
  IO.println s!"import graph analyzed ({suggestions} narrowing suggestions; no files changed)"
  return true

public def main (arguments : List String) : IO UInt32 := do
  if !arguments.isEmpty then
    IO.eprintln "usage: lake lint"
    return 64
  let noPlaceholders ← requireNoMatches
    "Lean sources contain forbidden proof placeholders"
    ("(^[[:space:]]*|(:=|by|exact)[[:space:]]+)" ++
      "(sor" ++ "ry|ad" ++ "mit)([[:space:]]|$)")
    #[]
    #["NormalForms", "Tests", "scripts"]
  let noCompilerTrust ← requireNoMatches
    "trusted Lean sources contain compiler/native trust primitives"
    ("native_" ++ "decide|Lean\\.of" ++ "Reduce|trust" ++ "Compiler")
    #["-g", "!NormalForms/Benchmarks/**", "-g", "!NormalForms/Tests/CertificateCLI.lean"]
    #["NormalForms"]
  let facadeIsNarrow ← requireNoMatches
    "the frozen facade imports a private, optional, application, or research module"
    ("^public import NormalForms\\.(Tests|Benchmarks|Research|External|" ++
      "Applications\\.(RationalCanonical|Homology))")
    #[]
    #["NormalForms.lean"]
  let whitespaceClean ← requireSuccess
    "git diff contains whitespace errors" "git" #["diff", "--check"]
  let importsAnalyzed ← checkImports
  if noPlaceholders && noCompilerTrust && facadeIsNarrow && whitespaceClean && importsAnalyzed then
    IO.println "repository lint passed"
    return 0
  return 1
