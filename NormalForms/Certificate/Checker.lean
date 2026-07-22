/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Certificate.Raw
public import NormalForms.Euclidean.Int
public import NormalForms.Matrix.Hermite.Defs
public import NormalForms.Matrix.Smith.Defs

/-!
# Pure integer certificate checker

This module is the trusted validation seam for untrusted HNF and SNF data.
The public checked structures contain data only. Internally, successful
validation also retains the proofs needed by `checkHNF_sound` and
`checkSNF_sound`.
-/

public section

namespace NormalForms.Certificate

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith

/-- Matrix fields named by dimension errors. -/
public inductive MatrixField where
  | input
  | U
  | UInverse
  | H
  | S
  | V
  | VInverse
  deriving Repr, DecidableEq

/-- A transformation matrix named by an inverse-equation error. -/
public inductive TransformMatrix where
  | U
  | V
  deriving Repr, DecidableEq

/-- Mathematical certificate failures, separate from JSON/parser failures. -/
public inductive CertError where
  | dimensions
      (field : MatrixField)
      (expectedRows expectedCols : Nat)
      (actualRows actualCols actualEntries : Nat)
  | inputMismatch
  | transformationEquation
  | leftInverse (matrix : TransformMatrix)
  | rightInverse (matrix : TransformMatrix)
  | normalForm
  deriving Repr, DecidableEq

/-- Type-checked HNF certificate data. Mathematical meaning comes from soundness. -/
public structure CheckedHNFData (m n : Nat) where
  U : Matrix (Fin m) (Fin m) Int
  UInverse : Matrix (Fin m) (Fin m) Int
  H : Matrix (Fin m) (Fin n) Int
  deriving Repr, DecidableEq

/-- Type-checked SNF certificate data. Mathematical meaning comes from soundness. -/
public structure CheckedSNFData (m n : Nat) where
  U : Matrix (Fin m) (Fin m) Int
  UInverse : Matrix (Fin m) (Fin m) Int
  S : Matrix (Fin m) (Fin n) Int
  V : Matrix (Fin n) (Fin n) Int
  VInverse : Matrix (Fin n) (Fin n) Int
  deriving Repr, DecidableEq

private def RawMatrix.toMatrix (raw : RawMatrix) (m n : Nat) :
    Matrix (Fin m) (Fin n) Int :=
  fun i j => raw.entries.getD (i.val * n + j.val) 0

private def allFin : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => true
  | _ + 1, predicate =>
      predicate 0 && allFin (fun i => predicate i.succ)

private theorem allFin_sound {n : Nat} {predicate : Fin n → Bool}
    (success : allFin predicate = true) :
    ∀ i, predicate i = true := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [allFin, Bool.and_eq_true] at success
      intro i
      refine Fin.cases success.1 ?_ i
      intro j
      exact ih success.2 j

private def matrixEqb {m n : Nat}
    (left right : Matrix (Fin m) (Fin n) Int) : Bool :=
  allFin fun i => allFin fun j => decide (left i j = right i j)

private theorem matrixEqb_sound {m n : Nat}
    {left right : Matrix (Fin m) (Fin n) Int}
    (success : matrixEqb left right = true) :
    left = right := by
  ext i j
  exact of_decide_eq_true (allFin_sound (allFin_sound success i) j)

private def checkDimensions
    (field : MatrixField) (expectedRows expectedCols : Nat)
    (raw : RawMatrix) : Except CertError Unit :=
  if raw.rows == expectedRows &&
      raw.cols == expectedCols &&
      raw.entries.size == expectedRows * expectedCols then
    .ok ()
  else
    .error (.dimensions field expectedRows expectedCols
      raw.rows raw.cols raw.entries.size)

private def dimensionsB
    (expectedRows expectedCols : Nat) (raw : RawMatrix) : Bool :=
  raw.rows == expectedRows &&
    raw.cols == expectedCols &&
    raw.entries.size == expectedRows * expectedCols

private theorem checkDimensions_eq_ok_of_dimensionsB
    (field : MatrixField) (expectedRows expectedCols : Nat)
    (raw : RawMatrix)
    (success : dimensionsB expectedRows expectedCols raw = true) :
    checkDimensions field expectedRows expectedCols raw = .ok () := by
  unfold dimensionsB at success
  simp only [Bool.and_eq_true] at success
  simp [checkDimensions, success.1.1, success.1.2, success.2]

private def reducedRowDecidable {m n : Nat}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) Int) (i : Fin m) :
    Decidable
      (match firstNonzero? (fun j : Fin n => A i.succ j.succ) with
      | none => True
      | some j => A 0 j.succ = A 0 j.succ % A i.succ j.succ) := by
  cases hFirst : firstNonzero? (fun j : Fin n => A i.succ j.succ) with
  | none =>
      exact isTrue trivial
  | some j =>
      exact inferInstance

/--
Proof-producing executable recognition of the recursive integer HNF
predicate. Returning an option avoids introducing a global proposition
decider; only successful validation is consumed by the checker.
-/
private def hermiteProof? :
    {m n : Nat} → (A : Matrix (Fin m) (Fin n) Int) →
      Option (PLift (IsHermiteNormalFormFin A))
  | 0, n, A =>
      some ⟨.emptyRows A⟩
  | m + 1, 0, A =>
      some ⟨.emptyCols A⟩
  | m + 1, n + 1, A =>
      if hzero : ∀ i, A i 0 = 0 then
        match hermiteProof? (tailCols A) with
        | none => none
        | some ⟨hTail⟩ => some ⟨.zeroCol A hzero hTail⟩
      else if hpivot : A 0 0 ≠ 0 then
        if hnorm : A 0 0 = normalize (A 0 0) then
          if hbelow : ∀ i : Fin m, A i.succ 0 = 0 then
            match hermiteProof? (lowerRight A) with
            | none => none
            | some ⟨hLower⟩ =>
                letI (i : Fin m) := reducedRowDecidable A i
                if hreduced : ∀ i : Fin m,
                    match firstNonzero? (fun j : Fin n => A i.succ j.succ) with
                    | none => True
                    | some j =>
                        A 0 j.succ = A 0 j.succ % A i.succ j.succ then
                  some ⟨.pivot A hpivot hnorm hbelow hLower hreduced⟩
                else
                  none
          else
            none
        else
          none
      else
        none
termination_by m n _ => m + n
decreasing_by
  · exact Nat.add_lt_add_left (Nat.lt_succ_self n) (m + 1)
  · exact Nat.add_lt_add (Nat.lt_succ_self m) (Nat.lt_succ_self n)

/-- Proof-producing executable recognition of the recursive integer SNF predicate. -/
private def smithProof? :
    {m n : Nat} → (A : Matrix (Fin m) (Fin n) Int) →
      Option (PLift (IsSmithNormalFormFin A))
  | 0, n, A =>
      some ⟨.emptyRows A⟩
  | m + 1, 0, A =>
      some ⟨.emptyCols A⟩
  | m + 1, n + 1, A =>
      if hzero : A 0 0 = 0 then
        if hrow : ∀ j : Fin n, A 0 j.succ = 0 then
          if hcol : ∀ i : Fin m, A i.succ 0 = 0 then
            if hLowerZero : matrixEqb (lowerRight A) 0 = true then
              some ⟨.zeroLead A hzero hrow hcol (matrixEqb_sound hLowerZero)⟩
            else
              none
          else
            none
        else
          none
      else if hnorm : A 0 0 = normalize (A 0 0) then
        if hrow : ∀ j : Fin n, A 0 j.succ = 0 then
          if hcol : ∀ i : Fin m, A i.succ 0 = 0 then
            match smithProof? (lowerRight A) with
            | none => none
            | some ⟨hLower⟩ =>
                if hdiv : ∀ i : Fin m, ∀ j : Fin n,
                    A 0 0 ∣ A i.succ j.succ then
                  some ⟨.pivot A hzero hnorm hrow hcol hLower hdiv⟩
                else
                  none
          else
            none
        else
          none
      else
        none
termination_by m n _ => m + n

/--
Independently reducible HNF kernel checks. The emitter gives every field its
own `decide_cbv` theorem so large certificates are never one monolithic
reduction.
-/
public structure HNFKernelChecks where
  inputDimensions : Bool
  UDimensions : Bool
  UInverseDimensions : Bool
  resultDimensions : Bool
  input : Bool
  equation : Bool
  leftInverse : Bool
  rightInverse : Bool
  normalForm : Bool
  deriving Repr, DecidableEq

/-- Independently reducible SNF kernel checks. -/
public structure SNFKernelChecks where
  inputDimensions : Bool
  UDimensions : Bool
  UInverseDimensions : Bool
  resultDimensions : Bool
  VDimensions : Bool
  VInverseDimensions : Bool
  input : Bool
  equation : Bool
  ULeftInverse : Bool
  URightInverse : Bool
  VLeftInverse : Bool
  VRightInverse : Bool
  normalForm : Bool
  deriving Repr, DecidableEq

/-- Compute the strict HNF import obligations without trusting the generator. -/
public def hnfKernelChecks {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int)
    (raw : RawHNFCertificate) : HNFKernelChecks :=
  let input := raw.input.toMatrix m n
  let U := raw.U.toMatrix m m
  let UInverse := raw.UInverse.toMatrix m m
  let H := raw.H.toMatrix m n
  { inputDimensions := dimensionsB m n raw.input
    UDimensions := dimensionsB m m raw.U
    UInverseDimensions := dimensionsB m m raw.UInverse
    resultDimensions := dimensionsB m n raw.H
    input := matrixEqb input expected
    equation := matrixEqb (U * expected) H
    leftInverse := matrixEqb (UInverse * U) 1
    rightInverse := matrixEqb (U * UInverse) 1
    normalForm := (hermiteProof? H).isSome }

/-- Compute the strict SNF import obligations without trusting the generator. -/
public def snfKernelChecks {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int)
    (raw : RawSNFCertificate) : SNFKernelChecks :=
  let input := raw.input.toMatrix m n
  let U := raw.U.toMatrix m m
  let UInverse := raw.UInverse.toMatrix m m
  let S := raw.S.toMatrix m n
  let V := raw.V.toMatrix n n
  let VInverse := raw.VInverse.toMatrix n n
  { inputDimensions := dimensionsB m n raw.input
    UDimensions := dimensionsB m m raw.U
    UInverseDimensions := dimensionsB m m raw.UInverse
    resultDimensions := dimensionsB m n raw.S
    VDimensions := dimensionsB n n raw.V
    VInverseDimensions := dimensionsB n n raw.VInverse
    input := matrixEqb input expected
    equation := matrixEqb (U * expected * V) S
    ULeftInverse := matrixEqb (UInverse * U) 1
    URightInverse := matrixEqb (U * UInverse) 1
    VLeftInverse := matrixEqb (VInverse * V) 1
    VRightInverse := matrixEqb (V * VInverse) 1
    normalForm := (smithProof? S).isSome }

/-- Kernel evidence assembled from separately reduced HNF obligations. -/
public structure HNFKernelEvidence (checks : HNFKernelChecks) : Prop where
  inputDimensions : checks.inputDimensions = true
  UDimensions : checks.UDimensions = true
  UInverseDimensions : checks.UInverseDimensions = true
  resultDimensions : checks.resultDimensions = true
  input : checks.input = true
  equation : checks.equation = true
  leftInverse : checks.leftInverse = true
  rightInverse : checks.rightInverse = true
  normalForm : checks.normalForm = true

/-- Kernel evidence assembled from separately reduced SNF obligations. -/
public structure SNFKernelEvidence (checks : SNFKernelChecks) : Prop where
  inputDimensions : checks.inputDimensions = true
  UDimensions : checks.UDimensions = true
  UInverseDimensions : checks.UInverseDimensions = true
  resultDimensions : checks.resultDimensions = true
  VDimensions : checks.VDimensions = true
  VInverseDimensions : checks.VInverseDimensions = true
  input : checks.input = true
  equation : checks.equation = true
  ULeftInverse : checks.ULeftInverse = true
  URightInverse : checks.URightInverse = true
  VLeftInverse : checks.VLeftInverse = true
  VRightInverse : checks.VRightInverse = true
  normalForm : checks.normalForm = true

private structure ValidatedHNFData {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int) where
  U : Matrix (Fin m) (Fin m) Int
  UInverse : Matrix (Fin m) (Fin m) Int
  H : Matrix (Fin m) (Fin n) Int
  equation : U * expected = H
  leftInverse : UInverse * U = 1
  rightInverse : U * UInverse = 1
  isHermite : IsHermiteNormalFormFin H

private structure ValidatedSNFData {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int) where
  U : Matrix (Fin m) (Fin m) Int
  UInverse : Matrix (Fin m) (Fin m) Int
  S : Matrix (Fin m) (Fin n) Int
  V : Matrix (Fin n) (Fin n) Int
  VInverse : Matrix (Fin n) (Fin n) Int
  equation : U * expected * V = S
  ULeftInverse : UInverse * U = 1
  URightInverse : U * UInverse = 1
  VLeftInverse : VInverse * V = 1
  VRightInverse : V * VInverse = 1
  isSmith : IsSmithNormalFormFin S

private def validateHNF {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int)
    (raw : RawHNFCertificate) :
    Except CertError (ValidatedHNFData expected) := do
  checkDimensions .input m n raw.input
  checkDimensions .U m m raw.U
  checkDimensions .UInverse m m raw.UInverse
  checkDimensions .H m n raw.H
  let input := raw.input.toMatrix m n
  let U := raw.U.toMatrix m m
  let UInverse := raw.UInverse.toMatrix m m
  let H := raw.H.toMatrix m n
  if _hInput : matrixEqb input expected = true then
    if hEquation : matrixEqb (U * expected) H = true then
      if hLeft : matrixEqb (UInverse * U) 1 = true then
        if hRight : matrixEqb (U * UInverse) 1 = true then
          match hermiteProof? H with
          | none => throw .normalForm
          | some ⟨isHermite⟩ =>
              return { U := U
                       UInverse := UInverse
                       H := H
                       equation := matrixEqb_sound hEquation
                       leftInverse := matrixEqb_sound hLeft
                       rightInverse := matrixEqb_sound hRight
                       isHermite := isHermite }
        else
          throw (.rightInverse .U)
      else
        throw (.leftInverse .U)
    else
      throw .transformationEquation
  else
    throw .inputMismatch

private def validateSNF {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int)
    (raw : RawSNFCertificate) :
    Except CertError (ValidatedSNFData expected) := do
  checkDimensions .input m n raw.input
  checkDimensions .U m m raw.U
  checkDimensions .UInverse m m raw.UInverse
  checkDimensions .S m n raw.S
  checkDimensions .V n n raw.V
  checkDimensions .VInverse n n raw.VInverse
  let input := raw.input.toMatrix m n
  let U := raw.U.toMatrix m m
  let UInverse := raw.UInverse.toMatrix m m
  let S := raw.S.toMatrix m n
  let V := raw.V.toMatrix n n
  let VInverse := raw.VInverse.toMatrix n n
  if _hInput : matrixEqb input expected = true then
    if hEquation : matrixEqb (U * expected * V) S = true then
      if hULeft : matrixEqb (UInverse * U) 1 = true then
        if hURight : matrixEqb (U * UInverse) 1 = true then
          if hVRight : matrixEqb (V * VInverse) 1 = true then
            if hVLeft : matrixEqb (VInverse * V) 1 = true then
              match smithProof? S with
              | none => throw .normalForm
              | some ⟨isSmith⟩ =>
                  return { U := U
                           UInverse := UInverse
                           S := S
                           V := V
                           VInverse := VInverse
                           equation := matrixEqb_sound hEquation
                           ULeftInverse := matrixEqb_sound hULeft
                           URightInverse := matrixEqb_sound hURight
                           VLeftInverse := matrixEqb_sound hVLeft
                           VRightInverse := matrixEqb_sound hVRight
                           isSmith := isSmith }
            else
              throw (.leftInverse .V)
          else
            throw (.rightInverse .V)
        else
          throw (.rightInverse .U)
      else
        throw (.leftInverse .U)
    else
      throw .transformationEquation
  else
    throw .inputMismatch

/-- Check an untrusted HNF payload against the caller-supplied expected matrix. -/
public def checkHNF {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int)
    (raw : RawHNFCertificate) :
    Except CertError (CheckedHNFData m n) :=
  (validateHNF expected raw).map fun validated =>
    { U := validated.U
      UInverse := validated.UInverse
      H := validated.H }

/-- Check an untrusted SNF payload against the caller-supplied expected matrix. -/
public def checkSNF {m n : Nat}
    (expected : Matrix (Fin m) (Fin n) Int)
    (raw : RawSNFCertificate) :
    Except CertError (CheckedSNFData m n) :=
  (validateSNF expected raw).map fun validated =>
    { U := validated.U
      UInverse := validated.UInverse
      S := validated.S
      V := validated.V
      VInverse := validated.VInverse }

/--
Combine separately reduced HNF kernel obligations into success of the pure
checker. The strong result is still obtained only from `checkHNF_sound`.
-/
public theorem checkHNF_isOk_of_kernelEvidence {m n : Nat}
    {expected : Matrix (Fin m) (Fin n) Int}
    {raw : RawHNFCertificate}
    (evidence : HNFKernelEvidence (hnfKernelChecks expected raw)) :
    (checkHNF expected raw).isOk = true := by
  have hInputDimensions : dimensionsB m n raw.input = true := by
    simpa only [hnfKernelChecks] using evidence.inputDimensions
  have hUDimensions : dimensionsB m m raw.U = true := by
    simpa only [hnfKernelChecks] using evidence.UDimensions
  have hUInverseDimensions : dimensionsB m m raw.UInverse = true := by
    simpa only [hnfKernelChecks] using evidence.UInverseDimensions
  have hResultDimensions : dimensionsB m n raw.H = true := by
    simpa only [hnfKernelChecks] using evidence.resultDimensions
  have hInput :
      matrixEqb (raw.input.toMatrix m n) expected = true := by
    simpa only [hnfKernelChecks] using evidence.input
  have hEquation :
      matrixEqb (raw.U.toMatrix m m * expected) (raw.H.toMatrix m n) = true := by
    simpa only [hnfKernelChecks] using evidence.equation
  have hLeft :
      matrixEqb
        (raw.UInverse.toMatrix m m * raw.U.toMatrix m m) 1 = true := by
    simpa only [hnfKernelChecks] using evidence.leftInverse
  have hRight :
      matrixEqb
        (raw.U.toMatrix m m * raw.UInverse.toMatrix m m) 1 = true := by
    simpa only [hnfKernelChecks] using evidence.rightInverse
  have hNormal :
      (hermiteProof? (raw.H.toMatrix m n)).isSome = true := by
    simpa only [hnfKernelChecks] using evidence.normalForm
  unfold checkHNF validateHNF
  rw [checkDimensions_eq_ok_of_dimensionsB .input m n raw.input
      hInputDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .U m m raw.U hUDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .UInverse m m raw.UInverse
      hUInverseDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .H m n raw.H hResultDimensions]
  simp only [hInput, ↓reduceDIte, hEquation, hLeft, hRight]
  cases hProof : hermiteProof? (raw.H.toMatrix m n) with
  | none =>
      simp only [hProof, Option.isSome_none, Bool.false_eq_true] at hNormal
  | some proof =>
      rfl

/--
Combine separately reduced SNF kernel obligations into success of the pure
checker. The strong result is still obtained only from `checkSNF_sound`.
-/
public theorem checkSNF_isOk_of_kernelEvidence {m n : Nat}
    {expected : Matrix (Fin m) (Fin n) Int}
    {raw : RawSNFCertificate}
    (evidence : SNFKernelEvidence (snfKernelChecks expected raw)) :
    (checkSNF expected raw).isOk = true := by
  have hInputDimensions : dimensionsB m n raw.input = true := by
    simpa only [snfKernelChecks] using evidence.inputDimensions
  have hUDimensions : dimensionsB m m raw.U = true := by
    simpa only [snfKernelChecks] using evidence.UDimensions
  have hUInverseDimensions : dimensionsB m m raw.UInverse = true := by
    simpa only [snfKernelChecks] using evidence.UInverseDimensions
  have hResultDimensions : dimensionsB m n raw.S = true := by
    simpa only [snfKernelChecks] using evidence.resultDimensions
  have hVDimensions : dimensionsB n n raw.V = true := by
    simpa only [snfKernelChecks] using evidence.VDimensions
  have hVInverseDimensions : dimensionsB n n raw.VInverse = true := by
    simpa only [snfKernelChecks] using evidence.VInverseDimensions
  have hInput :
      matrixEqb (raw.input.toMatrix m n) expected = true := by
    simpa only [snfKernelChecks] using evidence.input
  have hEquation :
      matrixEqb
        (raw.U.toMatrix m m * expected * raw.V.toMatrix n n)
        (raw.S.toMatrix m n) = true := by
    simpa only [snfKernelChecks] using evidence.equation
  have hULeft :
      matrixEqb
        (raw.UInverse.toMatrix m m * raw.U.toMatrix m m) 1 = true := by
    simpa only [snfKernelChecks] using evidence.ULeftInverse
  have hURight :
      matrixEqb
        (raw.U.toMatrix m m * raw.UInverse.toMatrix m m) 1 = true := by
    simpa only [snfKernelChecks] using evidence.URightInverse
  have hVLeft :
      matrixEqb
        (raw.VInverse.toMatrix n n * raw.V.toMatrix n n) 1 = true := by
    simpa only [snfKernelChecks] using evidence.VLeftInverse
  have hVRight :
      matrixEqb
        (raw.V.toMatrix n n * raw.VInverse.toMatrix n n) 1 = true := by
    simpa only [snfKernelChecks] using evidence.VRightInverse
  have hNormal :
      (smithProof? (raw.S.toMatrix m n)).isSome = true := by
    simpa only [snfKernelChecks] using evidence.normalForm
  unfold checkSNF validateSNF
  rw [checkDimensions_eq_ok_of_dimensionsB .input m n raw.input
      hInputDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .U m m raw.U hUDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .UInverse m m raw.UInverse
      hUInverseDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .S m n raw.S hResultDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .V n n raw.V hVDimensions]
  rw [checkDimensions_eq_ok_of_dimensionsB .VInverse n n raw.VInverse
      hVInverseDimensions]
  simp only [hInput, ↓reduceDIte, hEquation, hULeft,
    hURight, hVRight, hVLeft]
  cases hProof : smithProof? (raw.S.toMatrix m n) with
  | none =>
      simp only [hProof, Option.isSome_none, Bool.false_eq_true] at hNormal
  | some proof =>
      rfl

/-- A successful HNF check yields the strong explicit-inverse result. -/
public def checkHNF_sound {m n : Nat}
    {expected : Matrix (Fin m) (Fin n) Int}
    {raw : RawHNFCertificate}
    {checked : CheckedHNFData m n}
    (success : checkHNF expected raw = .ok checked) :
    HNFResultFin expected := by
  unfold checkHNF at success
  cases hValidated : validateHNF expected raw with
  | error error =>
      simp only [hValidated, Except.map] at success
      exact nomatch success
  | ok validated =>
      have hData :
          ({ U := validated.U
             UInverse := validated.UInverse
             H := validated.H } : CheckedHNFData m n) = checked := by
        simpa only [hValidated, Except.map, Except.ok.injEq] using success
      subst checked
      exact
        { U := validated.U
          U_cert :=
            { inverse := validated.UInverse
              left_inv := validated.leftInverse
              right_inv := validated.rightInverse }
          H := validated.H
          equation := validated.equation
          isHermite := validated.isHermite }

/-- A successful SNF check yields the strong explicit-inverse result. -/
public def checkSNF_sound {m n : Nat}
    {expected : Matrix (Fin m) (Fin n) Int}
    {raw : RawSNFCertificate}
    {checked : CheckedSNFData m n}
    (success : checkSNF expected raw = .ok checked) :
    SNFResultFin expected := by
  unfold checkSNF at success
  cases hValidated : validateSNF expected raw with
  | error error =>
      simp only [hValidated, Except.map] at success
      exact nomatch success
  | ok validated =>
      have hData :
          ({ U := validated.U
             UInverse := validated.UInverse
             S := validated.S
             V := validated.V
             VInverse := validated.VInverse } : CheckedSNFData m n) = checked := by
        simpa only [hValidated, Except.map, Except.ok.injEq] using success
      subst checked
      exact
        { U := validated.U
          U_cert :=
            { inverse := validated.UInverse
              left_inv := validated.ULeftInverse
              right_inv := validated.URightInverse }
          S := validated.S
          V := validated.V
          V_cert :=
            { inverse := validated.VInverse
              left_inv := validated.VLeftInverse
              right_inv := validated.VRightInverse }
          equation := validated.equation
          isSmith := validated.isSmith }

end NormalForms.Certificate
