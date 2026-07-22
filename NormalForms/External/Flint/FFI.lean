/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Certificate

/-!
# Optional FLINT FFI data adapter

This module is deliberately absent from the `NormalForms` facade. Its native
call returns only the canonical decimal worker protocol. The Lean layer parses
that output back through `normalforms.cert/v1`; mathematical conclusions still
come from the same pure certificate checker as the process-based CLI path.
-/

public section

namespace NormalForms.External.Flint

open NormalForms.Certificate

private def maxDimension : Nat :=
  4096

private def maxEntries : Nat :=
  16_777_216

public inductive Kind where
  | hnf
  | snf
  deriving Repr, DecidableEq

private def Kind.text : Kind → String
  | .hnf => "hnf"
  | .snf => "snf"

public inductive Error where
  | inputDimensions (rows cols entries : Nat)
  | native (detail : String)
  | protocol (detail : String)
  | schema (error : ParseError)
  | wrongKind
  | inputMismatch
  deriving Repr, DecidableEq

public inductive CheckError where
  | generator (error : Error)
  | checker (error : CertError)
  deriving Repr, DecidableEq

@[extern "normalforms_flint_ffi_run"]
private opaque runNative (request : @& String) : IO (Except String String)

/--
Run the shared `normalforms.decimal/v1` implementation through Lean's native
FFI. This is raw untrusted data and performs no checking.
-/
public def runRawProtocol (request : String) : IO (Except String String) :=
  runNative request

private def validateInput (input : RawMatrix) : Except Error Unit := do
  if input.rows > maxDimension ||
      input.cols > maxDimension ||
      input.rows * input.cols > maxEntries ||
      input.entries.size != input.rows * input.cols then
    throw (.inputDimensions input.rows input.cols input.entries.size)

private def renderRequest (kind : Kind) (input : RawMatrix) : String :=
  String.intercalate "\n" <|
    ["normalforms.decimal/v1",
      "kind " ++ kind.text,
      "rows " ++ toString input.rows,
      "cols " ++ toString input.cols,
      "entries " ++ toString input.entries.size] ++
      input.entries.toList.map toString ++
      ["end", ""]

private def asciiDigit (character : Char) : Bool :=
  decide ('0' ≤ character ∧ character ≤ '9')

private def nonzeroAsciiDigit (character : Char) : Bool :=
  decide ('1' ≤ character ∧ character ≤ '9')

private def canonicalUnsigned (value : String) : Bool :=
  match value.toList with
  | ['0'] => true
  | first :: rest => nonzeroAsciiDigit first && rest.all asciiDigit
  | [] => false

private def canonicalInteger (value : String) : Bool :=
  match value.toList with
  | ['0'] => true
  | '-' :: first :: rest =>
      nonzeroAsciiDigit first && rest.all asciiDigit
  | first :: rest => nonzeroAsciiDigit first && rest.all asciiDigit
  | [] => false

private def parseUnsigned? (value : String) : Option Nat :=
  if canonicalUnsigned value then value.toNat? else none

private structure ProtocolCursor where
  lines : Array String
  position : Nat := 0

private abbrev ProtocolParser :=
  StateT ProtocolCursor (Except Error)

private def protocolFailure {α : Type} (detail : String) :
    ProtocolParser α :=
  throw (.protocol detail)

private def takeLine (description : String) : ProtocolParser String := do
  let cursor ← get
  let some line := cursor.lines[cursor.position]?
    | protocolFailure s!"missing {description}"
  set { cursor with position := cursor.position + 1 }
  return line

private structure DecimalMatrix where
  rows : Nat
  cols : Nat
  entries : Array String

private def parseMatrix
    (expectedName : String) (expectedRows expectedCols : Nat) :
    ProtocolParser DecimalMatrix := do
  let header := (← takeLine s!"{expectedName} header").splitOn " "
  let ["matrix", name, rawRows, rawCols, rawCount] := header
    | protocolFailure s!"invalid {expectedName} matrix header"
  if name != expectedName then
    protocolFailure s!"expected matrix {expectedName}, got {name}"
  let some rows := parseUnsigned? rawRows
    | protocolFailure s!"invalid row count for {name}"
  let some cols := parseUnsigned? rawCols
    | protocolFailure s!"invalid column count for {name}"
  let some count := parseUnsigned? rawCount
    | protocolFailure s!"invalid entry count for {name}"
  if rows != expectedRows || cols != expectedCols ||
      count != rows * cols || count > maxEntries then
    protocolFailure s!"wrong dimensions or entry count for {name}"
  let mut entries := #[]
  for index in [0:count] do
    let entry ← takeLine s!"{name} entry {index}"
    if !canonicalInteger entry then
      protocolFailure s!"noncanonical integer in {name} at {index}"
    entries := entries.push entry
  return { rows, cols, entries }

private def renderJsonMatrix (matrix : DecimalMatrix) : String :=
  let entries :=
    matrix.entries.toList.map fun value => "\"" ++ value ++ "\""
  "{\"rows\":" ++ toString matrix.rows ++
    ",\"cols\":" ++ toString matrix.cols ++
    ",\"entries\":[" ++ String.intercalate "," entries ++ "]}"

private def renderJsonCertificate
    (kind : Kind) (matrices : List (String × DecimalMatrix)) : String :=
  let field (name : String) : String :=
    match matrices.lookup name with
    | some matrix => "\"" ++ name ++ "\":" ++ renderJsonMatrix matrix
    | none => "\"missing\":null"
  let matrixFields :=
    match kind with
    | .hnf => [field "input", field "U", field "UInverse", field "H"]
    | .snf =>
        [field "input", field "U", field "UInverse", field "S",
          field "V", field "VInverse"]
  let metadata :=
    "\"metadata\":{\"generator\":\"normalforms-flint-ffi\"," ++
      "\"flintVersion\":\"3.6.0\"," ++
      "\"build\":\"gmp=6.3.0;mpfr=4.2.2;" ++
      "link=dynamic;protocol=normalforms.decimal/v1\"}"
  "{" ++ String.intercalate ","
    (["\"schema\":\"normalforms.cert/v1\"",
      "\"kind\":\"" ++ kind.text ++ "\""] ++ matrixFields ++ [metadata]) ++ "}"

private def parseProtocol
    (kind : Kind) (expectedInput : RawMatrix) (source : String) :
    Except Error RawCertificate := do
  if source.contains '\r' || source.contains '\x00' ||
      !source.endsWith "\n" then
    throw (.protocol "output is not canonical LF-delimited text")
  let splitLines := source.splitOn "\n"
  let lines := splitLines.dropLast.toArray
  let parser : ProtocolParser (List (String × DecimalMatrix)) := do
    if (← takeLine "protocol header") != "normalforms.decimal/v1" then
      protocolFailure "wrong protocol header"
    if (← takeLine "kind") != "kind " ++ kind.text then
      protocolFailure "wrong result kind"
    if (← takeLine "FLINT version") != "flint 3.6.0" then
      protocolFailure "wrong FLINT version"
    let input ← parseMatrix "input" expectedInput.rows expectedInput.cols
    let U ← parseMatrix "U" expectedInput.rows expectedInput.rows
    let UInverse ←
      parseMatrix "UInverse" expectedInput.rows expectedInput.rows
    match kind with
    | .hnf =>
        let H ← parseMatrix "H" expectedInput.rows expectedInput.cols
        if (← takeLine "end marker") != "end" then
          protocolFailure "wrong end marker"
        return [("input", input), ("U", U), ("UInverse", UInverse), ("H", H)]
    | .snf =>
        let S ← parseMatrix "S" expectedInput.rows expectedInput.cols
        let V ← parseMatrix "V" expectedInput.cols expectedInput.cols
        let VInverse ←
          parseMatrix "VInverse" expectedInput.cols expectedInput.cols
        if (← takeLine "end marker") != "end" then
          protocolFailure "wrong end marker"
        return [("input", input), ("U", U), ("UInverse", UInverse), ("S", S),
          ("V", V), ("VInverse", VInverse)]
  let (matrices, cursor) ← parser.run { lines }
  if cursor.position != lines.size then
    throw (.protocol "trailing output after end marker")
  let certificate ←
    (parseCertificate (renderJsonCertificate kind matrices)).mapError .schema
  match kind, certificate with
  | Kind.hnf, RawCertificate.hnf certificate =>
      if certificate.input != expectedInput then
        throw .inputMismatch
      return RawCertificate.hnf certificate
  | Kind.snf, RawCertificate.snf certificate =>
      if certificate.input != expectedInput then
        throw .inputMismatch
      return RawCertificate.snf certificate
  | _, _ => throw .wrongKind

/-- Generate raw certificate data through the optional native FFI. -/
public def generate (kind : Kind) (input : RawMatrix) :
    IO (Except Error RawCertificate) := do
  match validateInput input with
  | .error error => return .error error
  | .ok () =>
      match ← runNative (renderRequest kind input) with
      | .error detail => return .error (.native detail)
      | .ok source => return parseProtocol kind input source

public def generateHNF (input : RawMatrix) :
    IO (Except Error RawHNFCertificate) := do
  match ← generate .hnf input with
  | .ok (.hnf certificate) => return .ok certificate
  | .ok _ => return .error .wrongKind
  | .error error => return .error error

public def generateSNF (input : RawMatrix) :
    IO (Except Error RawSNFCertificate) := do
  match ← generate .snf input with
  | .ok (.snf certificate) => return .ok certificate
  | .ok _ => return .error .wrongKind
  | .error error => return .error error

/--
Generate and pass HNF data through the same pure checker used by the CLI path.
The result remains checked data, not a proof or strong normal-form result.
-/
public def generateAndCheckHNF {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int) :
    IO (Except CheckError (CheckedHNFData m n)) := do
  match ← generateHNF (.ofMatrix expected) with
  | .error error => return .error (.generator error)
  | .ok raw =>
      return (checkHNF expected raw).mapError .checker

/--
Generate and pass SNF data through the same pure checker used by the CLI path.
The result remains checked data, not a proof or strong normal-form result.
-/
public def generateAndCheckSNF {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int) :
    IO (Except CheckError (CheckedSNFData m n)) := do
  match ← generateSNF (.ofMatrix expected) with
  | .error error => return .error (.generator error)
  | .ok raw =>
      return (checkSNF expected raw).mapError .checker

end NormalForms.External.Flint
