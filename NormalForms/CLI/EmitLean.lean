/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Certificate

public section

/-!
# Strict Lean certificate-module emitter

This module renders an already parsed `normalforms.cert/v1` payload as Lean
source. The generated module reduces every kernel obligation separately with
`decide_cbv` and obtains the strong result only through the public checker
soundness function.

The emitter is deliberately outside the `NormalForms` facade.
-/

namespace NormalForms.CLI.EmitLean

open NormalForms.Certificate

/-- User-controlled names needed by a generated certificate module. -/
structure Options where
  importModule : String
  matrixName : String
  declarationName : String
  deriving Repr, DecidableEq

/-- Source-generation failures before Lean kernel checking begins. -/
inductive Error where
  | invalidImportModule (value : String)
  | invalidMatrixName (value : String)
  | invalidDeclarationName (value : String)
  deriving Repr, DecidableEq

private def identifierStartCharacters : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_"

private def identifierRestCharacters : String :=
  identifierStartCharacters ++ "0123456789'"

private def reservedIdentifiers : List String :=
  ["as", "by", "class", "def", "deriving", "do", "else", "end", "export",
    "extends", "for", "forall", "from", "fun", "have", "if", "import", "in",
    "inductive", "instance", "let", "match", "module", "namespace", "open",
    "opaque", "private", "protected", "public", "section", "structure", "then",
    "theorem", "unsafe", "where", "with"]

private def emitterInternalNames : List String :=
  ["certificateRaw", "certificateChecks", "certificateInputDimensions",
    "certificateUDimensions", "certificateUInverseDimensions",
    "certificateResultDimensions", "certificateVDimensions",
    "certificateVInverseDimensions", "certificateInput",
    "certificateEquation", "certificateLeftInverse",
    "certificateRightInverse", "certificateULeftInverse",
    "certificateURightInverse", "certificateVLeftInverse",
    "certificateVRightInverse", "certificateNormalForm",
    "certificateEvidence"]

private def validIdentifierComponent (component : String) : Bool :=
  match component.toList with
  | [] => false
  | first :: rest =>
      identifierStartCharacters.contains first &&
        rest.all (fun character => identifierRestCharacters.contains character) &&
        !reservedIdentifiers.contains component

private def validQualifiedIdentifier (value : String) : Bool :=
  let components := value.splitOn "."
  !components.isEmpty && components.all validIdentifierComponent

private def renderOptionString : Option String → String
  | none => "none"
  | some value => "some " ++ reprStr value

private def renderMetadata (metadata : CertificateMetadata) : String :=
  "{ generator := " ++ renderOptionString metadata.generator ++
    ", flintVersion := " ++ renderOptionString metadata.flintVersion ++
    ", build := " ++ renderOptionString metadata.build ++
    ", hash := " ++ renderOptionString metadata.hash ++ " }"

private def renderEntries (entries : Array Int) : String :=
  "#[" ++ String.intercalate ", " (entries.toList.map toString) ++ "]"

private def renderMatrix (matrix : RawMatrix) : String :=
  "{ rows := " ++ toString matrix.rows ++
    ", cols := " ++ toString matrix.cols ++
    ", entries := " ++ renderEntries matrix.entries ++ " }"

private def renderHNF (certificate : RawHNFCertificate) : String :=
  "private def certificateRaw : RawHNFCertificate :=\n" ++
    "  { input := " ++ renderMatrix certificate.input ++ "\n" ++
    "    U := " ++ renderMatrix certificate.U ++ "\n" ++
    "    UInverse := " ++ renderMatrix certificate.UInverse ++ "\n" ++
    "    H := " ++ renderMatrix certificate.H ++ "\n" ++
    "    metadata := " ++ renderMetadata certificate.metadata ++ " }\n\n"

private def renderSNF (certificate : RawSNFCertificate) : String :=
  "private def certificateRaw : RawSNFCertificate :=\n" ++
    "  { input := " ++ renderMatrix certificate.input ++ "\n" ++
    "    U := " ++ renderMatrix certificate.U ++ "\n" ++
    "    UInverse := " ++ renderMatrix certificate.UInverse ++ "\n" ++
    "    S := " ++ renderMatrix certificate.S ++ "\n" ++
    "    V := " ++ renderMatrix certificate.V ++ "\n" ++
    "    VInverse := " ++ renderMatrix certificate.VInverse ++ "\n" ++
    "    metadata := " ++ renderMetadata certificate.metadata ++ " }\n\n"

private def renderObligation (name field : String) : String :=
  "private theorem certificate" ++ name ++ " :\n" ++
    "    certificateChecks." ++ field ++ " = true := by\n" ++
    "  decide_cbv\n\n"

private def renderHNFObligations : String :=
  renderObligation "InputDimensions" "inputDimensions" ++
  renderObligation "UDimensions" "UDimensions" ++
  renderObligation "UInverseDimensions" "UInverseDimensions" ++
  renderObligation "ResultDimensions" "resultDimensions" ++
  renderObligation "Input" "input" ++
  renderObligation "Equation" "equation" ++
  renderObligation "LeftInverse" "leftInverse" ++
  renderObligation "RightInverse" "rightInverse" ++
  renderObligation "NormalForm" "normalForm"

private def renderSNFObligations : String :=
  renderObligation "InputDimensions" "inputDimensions" ++
  renderObligation "UDimensions" "UDimensions" ++
  renderObligation "UInverseDimensions" "UInverseDimensions" ++
  renderObligation "ResultDimensions" "resultDimensions" ++
  renderObligation "VDimensions" "VDimensions" ++
  renderObligation "VInverseDimensions" "VInverseDimensions" ++
  renderObligation "Input" "input" ++
  renderObligation "Equation" "equation" ++
  renderObligation "ULeftInverse" "ULeftInverse" ++
  renderObligation "URightInverse" "URightInverse" ++
  renderObligation "VLeftInverse" "VLeftInverse" ++
  renderObligation "VRightInverse" "VRightInverse" ++
  renderObligation "NormalForm" "normalForm"

private def renderHNFEvidence : String :=
  "private theorem certificateEvidence :\n" ++
    "    HNFKernelEvidence certificateChecks :=\n" ++
    "  { inputDimensions := certificateInputDimensions\n" ++
    "    UDimensions := certificateUDimensions\n" ++
    "    UInverseDimensions := certificateUInverseDimensions\n" ++
    "    resultDimensions := certificateResultDimensions\n" ++
    "    input := certificateInput\n" ++
    "    equation := certificateEquation\n" ++
    "    leftInverse := certificateLeftInverse\n" ++
    "    rightInverse := certificateRightInverse\n" ++
    "    normalForm := certificateNormalForm }\n\n"

private def renderSNFEvidence : String :=
  "private theorem certificateEvidence :\n" ++
    "    SNFKernelEvidence certificateChecks :=\n" ++
    "  { inputDimensions := certificateInputDimensions\n" ++
    "    UDimensions := certificateUDimensions\n" ++
    "    UInverseDimensions := certificateUInverseDimensions\n" ++
    "    resultDimensions := certificateResultDimensions\n" ++
    "    VDimensions := certificateVDimensions\n" ++
    "    VInverseDimensions := certificateVInverseDimensions\n" ++
    "    input := certificateInput\n" ++
    "    equation := certificateEquation\n" ++
    "    ULeftInverse := certificateULeftInverse\n" ++
    "    URightInverse := certificateURightInverse\n" ++
    "    VLeftInverse := certificateVLeftInverse\n" ++
    "    VRightInverse := certificateVRightInverse\n" ++
    "    normalForm := certificateNormalForm }\n\n"

private def renderHeader (options : Options) : String :=
  "/-\n" ++
    "Generated by `normalforms-check emit-lean`.\n" ++
    "CLI success is not a theorem: compile this module with Lean's kernel.\n" ++
    "-/\n" ++
    "module\n\n" ++
    "public import NormalForms.Certificate\n" ++
    "public import " ++ options.importModule ++ "\n" ++
    "meta import all NormalForms.Certificate.Checker\n" ++
    "meta import all " ++ options.importModule ++ "\n\n" ++
    "public section\n\n" ++
    "set_option linter.style.longLine false\n\n" ++
    "open NormalForms.Certificate\n\n"

private def renderFooter : String :=
  ""

private def renderHNFResult (options : Options) : String :=
  "public def " ++ options.declarationName ++ " :\n" ++
    "    NormalForms.Matrix.Hermite.HNFResultFin " ++
      options.matrixName ++ " := by\n" ++
    "  have isOk :\n" ++
    "      (checkHNF " ++ options.matrixName ++
      " certificateRaw).isOk = true :=\n" ++
    "    checkHNF_isOk_of_kernelEvidence certificateEvidence\n" ++
    "  cases success : checkHNF " ++ options.matrixName ++
      " certificateRaw with\n" ++
    "  | error error =>\n" ++
    "      rw [success] at isOk\n" ++
    "      change false = true at isOk\n" ++
    "      exact (Bool.false_ne_true isOk).elim\n" ++
    "  | ok checked =>\n" ++
    "      exact checkHNF_sound success\n"

private def renderSNFResult (options : Options) : String :=
  "public def " ++ options.declarationName ++ " :\n" ++
    "    NormalForms.Matrix.Smith.SNFResultFin " ++
      options.matrixName ++ " := by\n" ++
    "  have isOk :\n" ++
    "      (checkSNF " ++ options.matrixName ++
      " certificateRaw).isOk = true :=\n" ++
    "    checkSNF_isOk_of_kernelEvidence certificateEvidence\n" ++
    "  cases success : checkSNF " ++ options.matrixName ++
      " certificateRaw with\n" ++
    "  | error error =>\n" ++
    "      rw [success] at isOk\n" ++
    "      change false = true at isOk\n" ++
    "      exact (Bool.false_ne_true isOk).elim\n" ++
    "  | ok checked =>\n" ++
    "      exact checkSNF_sound success\n"

/-- Render a strict kernel-import module for an HNF or SNF certificate. -/
def render (options : Options) (certificate : RawCertificate) :
    Except Error String := do
  if !validQualifiedIdentifier options.importModule then
    throw (.invalidImportModule options.importModule)
  if !validQualifiedIdentifier options.matrixName then
    throw (.invalidMatrixName options.matrixName)
  if !validQualifiedIdentifier options.declarationName ||
      emitterInternalNames.contains options.declarationName then
    throw (.invalidDeclarationName options.declarationName)
  let body :=
    match certificate with
    | .hnf certificate =>
        renderHNF certificate ++
          "private def certificateChecks : HNFKernelChecks :=\n" ++
          "  hnfKernelChecks " ++ options.matrixName ++ " certificateRaw\n\n" ++
          renderHNFObligations ++ renderHNFEvidence ++ renderHNFResult options
    | .snf certificate =>
        renderSNF certificate ++
          "private def certificateChecks : SNFKernelChecks :=\n" ++
          "  snfKernelChecks " ++ options.matrixName ++ " certificateRaw\n\n" ++
          renderSNFObligations ++ renderSNFEvidence ++ renderSNFResult options
  return renderHeader options ++ body ++ renderFooter

end NormalForms.CLI.EmitLean
