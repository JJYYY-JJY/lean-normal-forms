/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Basic

/-!
# Raw normal-form certificates

The `normalforms.cert/v1` parser is the only JSON seam in the trusted
certificate module. It accepts canonical decimal strings for matrix entries
and produces transport-neutral raw data. Dimension checks and mathematical
validation belong to the checker module.
-/

public section

namespace NormalForms.Certificate

open Lean

/-- Stable schema identifier for the first certificate format. -/
@[expose] public def schemaV1 : String :=
  "normalforms.cert/v1"

/-- The version 1 schema identifier is frozen as part of the stable API. -/
@[simp] public theorem schemaV1_eq : schemaV1 = "normalforms.cert/v1" :=
  rfl

/-- Parser failures are separated from mathematical certificate failures. -/
public inductive ParseError where
  | invalidJson (detail : String)
  | schema (path detail : String)
  | integer (path value : String)
  deriving Repr, DecidableEq

/-- Optional, untrusted provenance metadata. No field affects checking. -/
public structure CertificateMetadata where
  generator : Option String := none
  flintVersion : Option String := none
  build : Option String := none
  hash : Option String := none
  deriving Repr, DecidableEq

/-- A row-major integer matrix whose dimensions have not yet been trusted. -/
public structure RawMatrix where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, DecidableEq

/-- Untyped HNF certificate payload. -/
public structure RawHNFCertificate where
  input : RawMatrix
  U : RawMatrix
  UInverse : RawMatrix
  H : RawMatrix
  metadata : CertificateMetadata := {}
  deriving Repr, DecidableEq

/-- Untyped SNF certificate payload. -/
public structure RawSNFCertificate where
  input : RawMatrix
  U : RawMatrix
  UInverse : RawMatrix
  S : RawMatrix
  V : RawMatrix
  VInverse : RawMatrix
  metadata : CertificateMetadata := {}
  deriving Repr, DecidableEq

/-- Parsed certificate tagged by its normal-form kind. -/
public inductive RawCertificate where
  | hnf (certificate : RawHNFCertificate)
  | snf (certificate : RawSNFCertificate)
  deriving Repr, DecidableEq

private def digitValue? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

private def parseDigits : List Char → Option Nat
  | [] => none
  | digits =>
      digits.foldlM (init := 0) fun value digit => do
        let d ← digitValue? digit
        return value * 10 + d

/--
Parse exactly `0` or `-?[1-9][0-9]*`. This intentionally does not delegate to
a permissive numeric parser.
-/
private def parseCanonicalInt? (value : String) : Option Int :=
  match value.toList with
  | ['0'] => some 0
  | '-' :: first :: rest => do
      let firstValue ← digitValue? first
      if firstValue = 0 then
        none
      else
        let magnitude ← parseDigits (first :: rest)
        some (-(magnitude : Int))
  | first :: rest => do
      let firstValue ← digitValue? first
      if firstValue = 0 then
        none
      else
        let magnitude ← parseDigits (first :: rest)
        some (magnitude : Int)
  | _ => none

private def schemaError {α : Type _} (path detail : String) :
    Except ParseError α :=
  .error (.schema path detail)

private def required (json : Json) (path key : String) :
    Except ParseError Json :=
  match json.getObjVal? key with
  | .ok value => .ok value
  | .error detail => schemaError s!"{path}.{key}" detail

private def asObject (json : Json) (path : String) :
    Except ParseError (Std.TreeMap.Raw String Json compare) :=
  match json.getObj? with
  | .ok object => .ok object
  | .error detail => schemaError path detail

private def asString (json : Json) (path : String) :
    Except ParseError String :=
  match json.getStr? with
  | .ok value => .ok value
  | .error detail => schemaError path detail

private def asNat (json : Json) (path : String) :
    Except ParseError Nat :=
  match json.getNat? with
  | .ok value => .ok value
  | .error detail => schemaError path detail

private def asArray (json : Json) (path : String) :
    Except ParseError (Array Json) :=
  match json.getArr? with
  | .ok value => .ok value
  | .error detail => schemaError path detail

private def optionalString
    (object : Std.TreeMap.Raw String Json compare)
    (path key : String) : Except ParseError (Option String) :=
  match object.get? key with
  | none => .ok none
  | some value => some <$> asString value s!"{path}.{key}"

private def parseMetadata (json : Json) :
    Except ParseError CertificateMetadata := do
  let object ← asObject json "$.metadata"
  let generator ← optionalString object "$.metadata" "generator"
  let flintVersion ← optionalString object "$.metadata" "flintVersion"
  let build ← optionalString object "$.metadata" "build"
  let hash ← optionalString object "$.metadata" "hash"
  return { generator := generator
           flintVersion := flintVersion
           build := build
           hash := hash }

private def parseOptionalMetadata (root : Json) :
    Except ParseError CertificateMetadata := do
  let object ← asObject root "$"
  match object.get? "metadata" with
  | none => return ({} : CertificateMetadata)
  | some value => parseMetadata value

private def parseEntry (path : String) (json : Json) :
    Except ParseError Int := do
  let value ← asString json path
  match parseCanonicalInt? value with
  | some integer => return integer
  | none => throw (.integer path value)

private def parseMatrix (root : Json) (field : String) :
    Except ParseError RawMatrix := do
  let path := s!"$.{field}"
  let json ← required root "$" field
  let _ ← asObject json path
  let rows ← asNat (← required json path "rows") s!"{path}.rows"
  let cols ← asNat (← required json path "cols") s!"{path}.cols"
  let rawEntries ← asArray (← required json path "entries") s!"{path}.entries"
  let mut entries := #[]
  for h : index in [0:rawEntries.size] do
    entries := entries.push <|
      ← parseEntry s!"{path}.entries[{index}]" rawEntries[index]
  return { rows, cols, entries }

private def parseHNF (root : Json) :
    Except ParseError RawHNFCertificate := do
  let input ← parseMatrix root "input"
  let U ← parseMatrix root "U"
  let UInverse ← parseMatrix root "UInverse"
  let H ← parseMatrix root "H"
  let metadata ← parseOptionalMetadata root
  return { input := input
           U := U
           UInverse := UInverse
           H := H
           metadata := metadata }

private def parseSNF (root : Json) :
    Except ParseError RawSNFCertificate := do
  let input ← parseMatrix root "input"
  let U ← parseMatrix root "U"
  let UInverse ← parseMatrix root "UInverse"
  let S ← parseMatrix root "S"
  let V ← parseMatrix root "V"
  let VInverse ← parseMatrix root "VInverse"
  let metadata ← parseOptionalMetadata root
  return { input := input
           U := U
           UInverse := UInverse
           S := S
           V := V
           VInverse := VInverse
           metadata := metadata }

private def parseJsonCertificate (root : Json) :
    Except ParseError RawCertificate := do
  let _ ← asObject root "$"
  let schema ← asString (← required root "$" "schema") "$.schema"
  if schema != schemaV1 then
    throw (.schema "$.schema" s!"expected {schemaV1}, got {schema}")
  let kind ← asString (← required root "$" "kind") "$.kind"
  match kind with
  | "hnf" => return .hnf (← parseHNF root)
  | "snf" => return .snf (← parseSNF root)
  | other => throw (.schema "$.kind" s!"expected hnf or snf, got {other}")

/-- Parse a `normalforms.cert/v1` JSON certificate. -/
public def parseCertificate (input : String) :
    Except ParseError RawCertificate :=
  match Json.parse input with
  | .error detail => .error (.invalidJson detail)
  | .ok json => parseJsonCertificate json

/-- Construct raw row-major data from a typed matrix (primarily for adapters and tests). -/
public def RawMatrix.ofMatrix {m n : Nat}
    (matrix : Matrix (Fin m) (Fin n) Int) : RawMatrix :=
  { rows := m
    cols := n
    entries :=
      ((List.finRange m).flatMap fun i =>
        (List.finRange n).map fun j => matrix i j).toArray }

end NormalForms.Certificate
