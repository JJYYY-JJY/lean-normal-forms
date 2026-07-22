/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import Cli
import NormalForms.CLI.EmitLean

public section

/-!
# `normalforms-check`

The command-line front end currently exposes the strict `emit-lean` import
path. It parses untrusted JSON, renders a chunked `decide_cbv` module, and
leaves the decisive theorem check to a subsequent Lean compilation.
-/

open Cli
open NormalForms.Certificate

namespace NormalForms.CLI

private def missingFlag (name : String) : IO UInt32 := do
  IO.eprintln s!"normalforms-check: missing required flag --{name}"
  return 2

private def runEmitLean (parsed : Parsed) : IO UInt32 := do
  let some certificateFlag := parsed.flag? "certificate"
    | missingFlag "certificate"
  let some importFlag := parsed.flag? "import"
    | missingFlag "import"
  let some matrixFlag := parsed.flag? "matrix"
    | missingFlag "matrix"
  let some theoremFlag := parsed.flag? "theorem"
    | missingFlag "theorem"
  let certificatePath := certificateFlag.as! String
  let importModule := (importFlag.as! ModuleName).toString
  let matrixName := matrixFlag.as! String
  let declarationName := theoremFlag.as! String
  let input ←
    try
      IO.FS.readFile certificatePath
    catch error =>
      IO.eprintln s!"normalforms-check: cannot read {certificatePath}: {error}"
      return 2
  let certificate ←
    match parseCertificate input with
    | .ok certificate => pure certificate
    | .error error =>
        IO.eprintln s!"normalforms-check: certificate parse failed: {repr error}"
        return 2
  let source ←
    match EmitLean.render
        { importModule := importModule
          matrixName := matrixName
          declarationName := declarationName }
        certificate with
    | .ok source => pure source
    | .error error =>
        IO.eprintln s!"normalforms-check: source generation failed: {repr error}"
        return 2
  match parsed.flag? "output" with
  | none =>
      IO.print source
  | some outputFlag =>
      let outputPath := outputFlag.as! String
      try
        IO.FS.writeFile outputPath source
        IO.eprintln s!"normalforms-check: wrote {outputPath}"
      catch error =>
        IO.eprintln s!"normalforms-check: cannot write {outputPath}: {error}"
        return 2
  return 0

private def emitLeanCommand : Cmd := `[Cli|
  "emit-lean" VIA runEmitLean;
  "Render a strict Lean module from a normalforms.cert/v1 certificate."
  FLAGS:
    certificate : String; "Path to the JSON certificate."
    "import" : ModuleName; "Module defining the expected matrix."
    matrix : String; "Qualified name of the expected matrix."
    "theorem" : String; "Name of the generated strong-result declaration."
    output : String; "Optional destination; stdout is used when omitted."
  EXTENSIONS:
    require! #["certificate", "import", "matrix", "theorem"]
]

private def normalformsCheck : Cmd := `[Cli|
  "normalforms-check" NOOP; ["1.2.2"]
  "Parse certificates and emit strict Lean kernel-import modules."
  SUBCOMMANDS:
    emitLeanCommand
]

end NormalForms.CLI

public def main (args : List String) : IO UInt32 :=
  NormalForms.CLI.normalformsCheck.validate args
