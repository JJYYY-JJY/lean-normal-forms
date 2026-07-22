/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Certificate.Checker
import all NormalForms.Certificate.Checker
meta import all NormalForms.Certificate.Checker

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Certificate parser and checker regressions

The corpus exercises every stable parser/checker error category as well as
successful HNF and SNF reconstruction. Tests import the implementation with
`import all` so the guards reduce in the kernel; the public facade does not.
-/

namespace NormalForms.Tests.Certificate

open scoped Matrix
open NormalForms.Certificate

private def raw (rows cols : Nat) (entries : Array Int) : RawMatrix :=
  { rows, cols, entries }

public def expected : Matrix (Fin 1) (Fin 1) Int :=
  !![-6]

public def validHNF : RawHNFCertificate :=
  { input := raw 1 1 #[-6]
    U := raw 1 1 #[-1]
    UInverse := raw 1 1 #[-1]
    H := raw 1 1 #[6] }

public def validSNF : RawSNFCertificate :=
  { input := raw 1 1 #[-6]
    U := raw 1 1 #[-1]
    UInverse := raw 1 1 #[-1]
    S := raw 1 1 #[6]
    V := raw 1 1 #[1]
    VInverse := raw 1 1 #[1] }

private def hnfJson (inputEntry : String) : String :=
  "{\"schema\":\"normalforms.cert/v1\",\"kind\":\"hnf\"," ++
  "\"input\":{\"rows\":1,\"cols\":1,\"entries\":[\"" ++ inputEntry ++ "\"]}," ++
  "\"U\":{\"rows\":1,\"cols\":1,\"entries\":[\"-1\"]}," ++
  "\"UInverse\":{\"rows\":1,\"cols\":1,\"entries\":[\"-1\"]}," ++
  "\"H\":{\"rows\":1,\"cols\":1,\"entries\":[\"6\"]}," ++
  "\"metadata\":{\"generator\":\"test\",\"flintVersion\":\"3.6.0\"}}"

private def validSNFJson : String :=
  "{\"schema\":\"normalforms.cert/v1\",\"kind\":\"snf\"," ++
  "\"input\":{\"rows\":1,\"cols\":1,\"entries\":[\"-6\"]}," ++
  "\"U\":{\"rows\":1,\"cols\":1,\"entries\":[\"-1\"]}," ++
  "\"UInverse\":{\"rows\":1,\"cols\":1,\"entries\":[\"-1\"]}," ++
  "\"S\":{\"rows\":1,\"cols\":1,\"entries\":[\"6\"]}," ++
  "\"V\":{\"rows\":1,\"cols\":1,\"entries\":[\"1\"]}," ++
  "\"VInverse\":{\"rows\":1,\"cols\":1,\"entries\":[\"1\"]}}"

private def parsedValidHNF : Bool :=
  match parseCertificate (hnfJson "-6") with
  | .ok (.hnf certificate) =>
      certificate.input == validHNF.input &&
        certificate.U == validHNF.U &&
        certificate.UInverse == validHNF.UInverse &&
        certificate.H == validHNF.H &&
        certificate.metadata.generator == some "test" &&
        certificate.metadata.flintVersion == some "3.6.0"
  | _ => false

private def parsedValidSNF : Bool :=
  match parseCertificate validSNFJson with
  | .ok (.snf certificate) =>
      certificate.input == validSNF.input &&
        certificate.U == validSNF.U &&
        certificate.UInverse == validSNF.UInverse &&
        certificate.S == validSNF.S &&
        certificate.V == validSNF.V &&
        certificate.VInverse == validSNF.VInverse
  | _ => false

private def isIntegerError (entry : String) : Bool :=
  match parseCertificate (hnfJson entry) with
  | .error (.integer "$.input.entries[0]" value) => value == entry
  | _ => false

private def invalidJsonRejected : Bool :=
  match parseCertificate "{" with
  | .error (.invalidJson _) => true
  | _ => false

private def wrongSchemaRejected : Bool :=
  match parseCertificate
      ((hnfJson "-6").replace "normalforms.cert/v1" "normalforms.cert/v2") with
  | .error (.schema "$.schema" _) => true
  | _ => false

private def wrongKindRejected : Bool :=
  match parseCertificate
      ((hnfJson "-6").replace "\"hnf\"" "\"other\"") with
  | .error (.schema "$.kind" _) => true
  | _ => false

#guard parsedValidHNF
#guard parsedValidSNF
#guard invalidJsonRejected
#guard wrongSchemaRejected
#guard wrongKindRejected
#guard ["00", "-0", "+1", "01", " 1", "1 "].all isIntegerError

#guard (checkHNF expected validHNF).isOk
#guard (checkSNF expected validSNF).isOk

/-- Strict-kernel HNF reconstruction smoke test. -/
public def strictHNFResult :
    NormalForms.Matrix.Hermite.HNFResultFin expected := by
  have isOk : (checkHNF expected validHNF).isOk = true := by decide_cbv
  cases success : checkHNF expected validHNF with
  | error error =>
      rw [success] at isOk
      change false = true at isOk
      exact (Bool.false_ne_true isOk).elim
  | ok checked =>
      exact checkHNF_sound success

/-- Strict-kernel SNF reconstruction smoke test. -/
public def strictSNFResult :
    NormalForms.Matrix.Smith.SNFResultFin expected := by
  have isOk : (checkSNF expected validSNF).isOk = true := by decide_cbv
  cases success : checkSNF expected validSNF with
  | error error =>
      rw [success] at isOk
      change false = true at isOk
      exact (Bool.false_ne_true isOk).elim
  | ok checked =>
      exact checkSNF_sound success

private def dimensionFailure : RawHNFCertificate :=
  { validHNF with input := raw 2 1 #[-6] }

#guard checkHNF expected dimensionFailure ==
  .error (.dimensions .input 1 1 2 1 1)

private def inputMismatch : RawHNFCertificate :=
  { validHNF with input := raw 1 1 #[-7] }

#guard checkHNF expected inputMismatch == .error .inputMismatch

private def transformationFailure : RawHNFCertificate :=
  { validHNF with H := raw 1 1 #[5] }

#guard checkHNF expected transformationFailure == .error .transformationEquation

private def leftInverseFailure : RawHNFCertificate :=
  { validHNF with UInverse := raw 1 1 #[1] }

#guard checkHNF expected leftInverseFailure == .error (.leftInverse .U)

private def rightInverseFailure : RawSNFCertificate :=
  { validSNF with
    S := raw 1 1 #[0]
    V := raw 1 1 #[0]
    VInverse := raw 1 1 #[0] }

#guard checkSNF expected rightInverseFailure == .error (.rightInverse .V)

private def normalFormFailure : RawHNFCertificate :=
  { input := raw 1 1 #[-6]
    U := raw 1 1 #[1]
    UInverse := raw 1 1 #[1]
    H := raw 1 1 #[-6] }

#guard checkHNF expected normalFormFailure == .error .normalForm

private def otherExpected : Matrix (Fin 1) (Fin 1) Int :=
  !![-7]

#guard checkHNF otherExpected validHNF == .error .inputMismatch

private def zeroRows : Matrix (Fin 0) (Fin 2) Int := 0
private def zeroRowsHNF : RawHNFCertificate :=
  { input := raw 0 2 #[]
    U := raw 0 0 #[]
    UInverse := raw 0 0 #[]
    H := raw 0 2 #[] }

#guard (checkHNF zeroRows zeroRowsHNF).isOk

end NormalForms.Tests.Certificate
