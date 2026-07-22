/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Matrix.Elementary.Basic
import all NormalForms.Matrix.Certificates.Basic
import all NormalForms.Matrix.Certificates.ReversibleLog
import all NormalForms.Matrix.Hermite
import all NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Smith
import all NormalForms.Matrix.Smith.Transform
import all NormalForms.Matrix.Smith.Algorithm
import all NormalForms.Matrix.Smith.Uniqueness
import all NormalForms.Bridge.MathlibPID
import all NormalForms.Bridge.MathlibPID.Quotient
import all NormalForms.Applications.AbelianGroups
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Abelian Group Examples

Sample matrices for the current finitely generated abelian-group showcase.
The current module includes executable smoke checks for elementary matrices,
mixed log certificates, the Phase 1 Bezout reduction gadget, and Phase 2 HNF
smoke coverage.

For Smith normal form, the examples are intentionally split across two layers:

- internal `Fin`-indexed smoke theorems check concrete diagonal specifications,
  invariant factors, same-size `prepareLead...` / `stabilizePivot` /
  `improvePivot` building blocks, and witness/result checks over `Int` and
  `Q[X]`
- public smoke theorems exercise direct results with stored indexings and
  explicit inverse certificates
- bridge-facing smoke theorems instantiate the semantic PID bridge over `Int`,
  including quotient/direct-sum/`PiZMod` equivalences and normalized
  executable-vs-mathlib coefficient-list length comparisons in the full-rank
  examples
- application-facing smoke theorems instantiate the public Phase 5
  `NormalForms.Applications.AbelianGroups` API on full-rank, unit-boundary, and
  mixed torsion-plus-free presentation matrices

This split keeps the examples close to the public API while avoiding the costly
`Fintype.equivFin` simplification paths that can otherwise dominate elaboration
for concrete matrices.
-/

set_option linter.privateModule false

namespace NormalForms.Examples.AbelianGroups

open Polynomial
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith
open NormalForms.Bridge.MathlibPID
open NormalForms.Applications.AbelianGroups

def zeroMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  0

def fullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 0 => 3
    | 1, 1 => 5
    | _, _ => 0

def rankDeficientMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 4
    | 1, 0 => 1
    | 1, 1 => 2
    | _, _ => 0

def unitBoundaryMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => -1
    | 0, 1 => 0
    | 1, 0 => 0
    | 1, 1 => 2
    | _, _ => 0

def presentationMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 4
    | 0, 2 => 6
    | 1, 0 => 0
    | 1, 1 => 8
    | 1, 2 => 10
    | _, _ => 0

def swappedFullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 3
    | 0, 1 => 5
    | 1, 0 => 1
    | 1, 1 => 2
    | _, _ => 0

def rowAddedFullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 0 => 5
    | 1, 1 => 9
    | _, _ => 0

def rowScaledFullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 0 => -3
    | 1, 1 => -5
    | _, _ => 0

def swappedPresentationColumnsZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 6
    | 0, 1 => 4
    | 0, 2 => 2
    | 1, 0 => 10
    | 1, 1 => 8
    | 1, 2 => 0
    | _, _ => 0

def addedPresentationColumnsZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 2
    | 0, 2 => 6
    | 1, 0 => 0
    | 1, 1 => 8
    | 1, 2 => 10
    | _, _ => 0

def scaledPresentationColumnsZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 4
    | 0, 2 => -6
    | 1, 0 => 0
    | 1, 1 => 8
    | 1, 2 => -10
    | _, _ => 0

abbrev mixedLog : OperationLog Int (Fin 2) (Fin 3) :=
  [MatrixStep.row (.add (0 : Fin 2) (1 : Fin 2) 2),
    MatrixStep.col (.swap (0 : Fin 3) (2 : Fin 3))]

abbrev rowOnlyLog : OperationLog Int (Fin 2) (Fin 2) :=
  [MatrixStep.row (.add (0 : Fin 2) (1 : Fin 2) 2)]

abbrev mixedReversibleLog :
    NormalForms.Matrix.Certificates.ReversibleLog.ReversibleOperationLog
      Int (Fin 2) (Fin 3) :=
  [NormalForms.Matrix.Certificates.ReversibleLog.ReversibleStep.rowAdd
      (0 : Fin 2) (1 : Fin 2) 2 (by decide),
    NormalForms.Matrix.Certificates.ReversibleLog.ReversibleStep.columnSwap
      (0 : Fin 3) (2 : Fin 3)]

def mixedReplayMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 6
    | 0, 1 => 4
    | 0, 2 => 2
    | 1, 0 => 22
    | 1, 1 => 16
    | 1, 2 => 4
    | _, _ => 0

noncomputable def polynomialMatrixQX : _root_.Matrix (Fin 2) (Fin 2) (Polynomial Rat) :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => Polynomial.X + 1
    | 0, 1 => Polynomial.X
    | 1, 0 => 0
    | 1, 1 => Polynomial.X ^ 2 + 1
    | _, _ => 0

def fullRankHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 1]

def rankDeficientHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 2;
     0, 0]

def unitBoundaryHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 2]

def presentationHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![2, 4, 6;
     0, 8, 10]

def fullRankSNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 1]

def rankDeficientSNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 0]

def unitBoundarySNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 2]

def presentationSNFMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![2, 0, 0;
     0, 2, 0]

def mixedTorsionFreeMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![2, 0;
     0, 0]

noncomputable def simpleSmithMatrixQX : _root_.Matrix (Fin 2) (Fin 2) (Polynomial Rat) :=
  !![(1 : Polynomial Rat), 0;
     0, 1]

def prepareLeadColumnMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![6, 0;
     15, 0]

def prepareLeadRowMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![6, 15;
     0, 0]

def improvePivotMatrixZ : _root_.Matrix (Fin 3) (Fin 3) Int :=
  !![6, 0, 0;
     0, 0, 15;
     0, 0, 0]

def improvePivotLeadClearedStateZ :
    NormalForms.Matrix.Smith.Internal.LeadClearedState improvePivotMatrixZ :=
  { t := TwoSidedTransform.refl improvePivotMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simp [improvePivotMatrixZ, TwoSidedTransform.refl, Int.normalize_of_nonneg]
    rowCleared := by
      intro j
      fin_cases j <;> decide
    colCleared := by
      intro i
      fin_cases i <;> decide }

def prepareLeadColumnPivotStateZ :
    NormalForms.Matrix.Smith.Internal.PivotState prepareLeadColumnMatrixZ :=
  { t := TwoSidedTransform.refl prepareLeadColumnMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simp [prepareLeadColumnMatrixZ, TwoSidedTransform.refl, Int.normalize_of_nonneg] }

def prepareLeadRowPivotStateZ :
    NormalForms.Matrix.Smith.Internal.PivotState prepareLeadRowMatrixZ :=
  { t := TwoSidedTransform.refl prepareLeadRowMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simp [prepareLeadRowMatrixZ, TwoSidedTransform.refl, Int.normalize_of_nonneg] }

def fullRankSNFPivotStateZ :
    NormalForms.Matrix.Smith.Internal.PivotState fullRankSNFMatrixZ :=
  { t := TwoSidedTransform.refl fullRankSNFMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simp [fullRankSNFMatrixZ, TwoSidedTransform.refl] }

def fullRankSNFLeftZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![-5, 2;
     3, -1]

def rankDeficientSNFLeftZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![0, 1;
     1, -2]

def rankDeficientSNFRightZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, -2;
     0, 1]

def presentationSNFRightZ : _root_.Matrix (Fin 3) (Fin 3) Int :=
  !![1, -1, 2;
     0, -1, 5;
     0, 1, -4]

noncomputable def fullRankHNFPublic : HNFResult fullRankMatrixZ :=
  hermiteNormalForm fullRankMatrixZ

noncomputable abbrev fullRankHNFInternal :
    HNFResultFin fullRankMatrixZ :=
  hermiteNormalFormFin fullRankMatrixZ

private theorem hnfEqOfLeftCertificateInt {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (result : HNFResultFin A)
    (cert : LeftCertificate A)
    (hSpec : IsHermiteNormalFormFin cert.result) :
    result.H = cert.result := by
  have hRecover : result.U_cert.inverse * result.H = A := by
    calc
      result.U_cert.inverse * result.H =
          result.U_cert.inverse * (result.U * A) := by rw [result.equation]
      _ = (result.U_cert.inverse * result.U) * A := by
        rw [_root_.Matrix.mul_assoc]
      _ = A := by rw [result.U_cert.left_inv]; simp
  have hEq :
      (cert.U * result.U_cert.inverse) * result.H = cert.result := by
    calc
      (cert.U * result.U_cert.inverse) * result.H =
          cert.U * (result.U_cert.inverse * result.H) := by
            rw [_root_.Matrix.mul_assoc]
      _ = cert.U * A := by rw [hRecover]
      _ = cert.result := cert.equation
  exact isHermiteNormalFormFin_unique_of_left_equiv
    result.isHermite hSpec
    (U := cert.U * result.U_cert.inverse)
    (unimodular_mul cert.U_cert.unimodular result.U_cert.symm.unimodular)
    hEq

private theorem snfEqOfCertificateInt {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (result : SNFResultFin A)
    (cert : TwoSidedCertificate A)
    (hSpec : IsSmithNormalFormFin cert.result) :
    result.S = cert.result := by
  have hRecover :
      result.U_cert.inverse * result.S * result.V_cert.inverse = A := by
    calc
      result.U_cert.inverse * result.S * result.V_cert.inverse =
          result.U_cert.inverse * (result.U * A * result.V) *
            result.V_cert.inverse := by rw [result.equation]
      _ = (result.U_cert.inverse * result.U) * A *
          (result.V * result.V_cert.inverse) := by
            simp only [_root_.Matrix.mul_assoc]
      _ = A := by
            rw [result.U_cert.left_inv, result.V_cert.right_inv]
            simp
  have hEq :
      (cert.U * result.U_cert.inverse) * result.S *
          (result.V_cert.inverse * cert.V) = cert.result := by
    calc
      (cert.U * result.U_cert.inverse) * result.S *
          (result.V_cert.inverse * cert.V) =
          cert.U *
            (result.U_cert.inverse * result.S * result.V_cert.inverse) *
            cert.V := by simp only [_root_.Matrix.mul_assoc]
      _ = cert.U * A * cert.V := by rw [hRecover]
      _ = cert.result := cert.equation
  exact NormalForms.Matrix.Smith.Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
    result.isSmith hSpec
    (U := cert.U * result.U_cert.inverse)
    (V := result.V_cert.inverse * cert.V)
    (unimodular_mul cert.U_cert.unimodular result.U_cert.symm.unimodular)
    (unimodular_mul result.V_cert.symm.unimodular cert.V_cert.unimodular)
    hEq

private theorem fullRankHNFSpec :
    NormalForms.Matrix.Hermite.IsHermiteNormalFormFin fullRankHNFMatrixZ := by
  refine .pivot _ ?_ ?_ ?_ ?_ ?_
  · decide
  · simp [fullRankHNFMatrixZ]
  · intro i
    fin_cases i
    decide
  · refine .pivot _ ?_ ?_ ?_ ?_ ?_
    · decide
    · simp [fullRankHNFMatrixZ, lowerRight]
    · intro i
      exact Fin.elim0 i
    · exact .emptyRows _
    · intro i
      exact Fin.elim0 i
  · intro i
    fin_cases i
    simp [fullRankHNFMatrixZ, NormalForms.Matrix.Hermite.firstNonzero?]

private theorem rankDeficientHNFSpec :
    NormalForms.Matrix.Hermite.IsHermiteNormalFormFin rankDeficientHNFMatrixZ := by
  refine .pivot _ ?_ ?_ ?_ ?_ ?_
  · decide
  · simp [rankDeficientHNFMatrixZ]
  · intro i
    fin_cases i
    decide
  · refine .zeroCol _ ?_ ?_
    · intro i
      fin_cases i
      decide
    · simpa [tailCols, lowerRight, rankDeficientHNFMatrixZ] using
        (NormalForms.Matrix.Hermite.IsHermiteNormalFormFin.emptyCols
          (tailCols (lowerRight rankDeficientHNFMatrixZ)))
  · intro i
    fin_cases i
    simp [rankDeficientHNFMatrixZ]

private theorem unitBoundaryHNFSpec :
    NormalForms.Matrix.Hermite.IsHermiteNormalFormFin unitBoundaryHNFMatrixZ := by
  refine .pivot _ ?_ ?_ ?_ ?_ ?_
  · decide
  · simp [unitBoundaryHNFMatrixZ]
  · intro i
    fin_cases i
    decide
  · refine .pivot _ ?_ ?_ ?_ ?_ ?_
    · decide
    · simp [unitBoundaryHNFMatrixZ, lowerRight, Int.normalize_of_nonneg]
    · intro i
      exact Fin.elim0 i
    · exact .emptyRows _
    · intro i
      exact Fin.elim0 i
  · intro i
    fin_cases i
    simp [unitBoundaryHNFMatrixZ, NormalForms.Matrix.Hermite.firstNonzero?]

private theorem presentationHNFSpec :
    NormalForms.Matrix.Hermite.IsHermiteNormalFormFin presentationHNFMatrixZ := by
  refine .pivot _ ?_ ?_ ?_ ?_ ?_
  · decide
  · simp [presentationHNFMatrixZ, Int.normalize_of_nonneg]
  · intro i
    fin_cases i
    decide
  · refine .pivot _ ?_ ?_ ?_ ?_ ?_
    · decide
    · simp [presentationHNFMatrixZ, lowerRight, Int.normalize_of_nonneg]
    · intro i
      exact Fin.elim0 i
    · exact .emptyRows _
    · intro i
      exact Fin.elim0 i
  · intro i
    fin_cases i
    simp [presentationHNFMatrixZ, NormalForms.Matrix.Hermite.firstNonzero?]

private def fullRankSNFLeftInverseCertificate :
    MatrixInverseCertificate fullRankSNFLeftZ :=
  { inverse := fullRankMatrixZ
    left_inv := by decide
    right_inv := by decide }

def rankDeficientSNFLeftInvZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![2, 1;
     1, 0]

private def rankDeficientSNFLeftInverseCertificate :
    MatrixInverseCertificate rankDeficientSNFLeftZ :=
  { inverse := rankDeficientSNFLeftInvZ
    left_inv := by decide
    right_inv := by decide }

def rankDeficientSNFRightInvZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 2;
     0, 1]

private def rankDeficientSNFRightInverseCertificate :
    MatrixInverseCertificate rankDeficientSNFRightZ :=
  { inverse := rankDeficientSNFRightInvZ
    left_inv := by decide
    right_inv := by decide }

private def unitBoundaryRowOpInverseCertificate :
    MatrixInverseCertificate
      (rowOperationMatrix (.smul (0 : Fin 2) (-1)) :
        _root_.Matrix (Fin 2) (Fin 2) Int) :=
  { inverse := rowOperationMatrix (.smul (0 : Fin 2) (-1))
    left_inv := by decide
    right_inv := by decide }

def presentationSNFRightInvZ : _root_.Matrix (Fin 3) (Fin 3) Int :=
  !![1, 2, 3;
     0, 4, 5;
     0, 1, 1]

private theorem presentationSNFRightMulInv :
    presentationSNFRightZ * presentationSNFRightInvZ = 1 := by
  decide

private def presentationSNFRightInverseCertificate :
    MatrixInverseCertificate presentationSNFRightZ :=
  { inverse := presentationSNFRightInvZ
    left_inv := by decide
    right_inv := presentationSNFRightMulInv }

private theorem fullRankSNFLeftUnimodular : Unimodular fullRankSNFLeftZ :=
  fullRankSNFLeftInverseCertificate.unimodular

private theorem rankDeficientSNFLeftUnimodular : Unimodular rankDeficientSNFLeftZ :=
  rankDeficientSNFLeftInverseCertificate.unimodular

private theorem rankDeficientSNFRightUnimodular : Unimodular rankDeficientSNFRightZ :=
  rankDeficientSNFRightInverseCertificate.unimodular

private theorem unitBoundaryRowOpUnimodular :
    Unimodular
      (rowOperationMatrix (.smul (0 : Fin 2) (-1)) :
        _root_.Matrix (Fin 2) (Fin 2) Int) :=
  unitBoundaryRowOpInverseCertificate.unimodular

private theorem presentationSNFRightUnimodular : Unimodular presentationSNFRightZ :=
  presentationSNFRightInverseCertificate.unimodular

private def fullRankHNFCertificateZ : LeftCertificate fullRankMatrixZ :=
  { U := fullRankSNFLeftZ
    U_cert := fullRankSNFLeftInverseCertificate
    result := fullRankHNFMatrixZ
    equation := by decide }

private def rankDeficientHNFCertificateZ : LeftCertificate rankDeficientMatrixZ :=
  { U := rankDeficientSNFLeftZ
    U_cert := rankDeficientSNFLeftInverseCertificate
    result := rankDeficientHNFMatrixZ
    equation := by decide }

private def unitBoundaryHNFCertificateZ : LeftCertificate unitBoundaryMatrixZ :=
  { U := rowOperationMatrix (.smul (0 : Fin 2) (-1))
    U_cert := unitBoundaryRowOpInverseCertificate
    result := unitBoundaryHNFMatrixZ
    equation := by decide }

private def presentationHNFCertificateZ : LeftCertificate presentationMatrixZ :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    result := presentationHNFMatrixZ
    equation := by decide }

theorem zeroMatrixHNFSmoke :
    (hermiteNormalFormFin zeroMatrixZ).H = zeroMatrixZ := by
  let certificate : LeftCertificate zeroMatrixZ :=
    { U := 1
      U_cert := MatrixInverseCertificate.one
      result := zeroMatrixZ
      equation := by simp }
  have normal : IsHermiteNormalFormFin zeroMatrixZ := by
    refine .zeroCol _ ?_ ?_
    · intro row
      fin_cases row <;> rfl
    · refine .zeroCol _ ?_ ?_
      · intro row
        fin_cases row <;> rfl
      · exact .emptyCols _
  simpa [certificate] using hnfEqOfLeftCertificateInt
    (hermiteNormalFormFin zeroMatrixZ) certificate normal

theorem fullRankHNFSmoke :
    (hermiteNormalFormFin fullRankMatrixZ).H =
      fullRankHNFMatrixZ := by
  simpa [fullRankHNFCertificateZ] using hnfEqOfLeftCertificateInt
    (hermiteNormalFormFin fullRankMatrixZ)
    fullRankHNFCertificateZ
    fullRankHNFSpec

theorem rankDeficientHNFSmoke :
    (hermiteNormalFormFin rankDeficientMatrixZ).H =
      rankDeficientHNFMatrixZ := by
  simpa [rankDeficientHNFCertificateZ] using hnfEqOfLeftCertificateInt
    (hermiteNormalFormFin rankDeficientMatrixZ)
    rankDeficientHNFCertificateZ
    rankDeficientHNFSpec

theorem unitBoundaryHNFSmoke :
    (hermiteNormalFormFin unitBoundaryMatrixZ).H =
      unitBoundaryHNFMatrixZ := by
  simpa [unitBoundaryHNFCertificateZ] using hnfEqOfLeftCertificateInt
    (hermiteNormalFormFin unitBoundaryMatrixZ)
    unitBoundaryHNFCertificateZ
    unitBoundaryHNFSpec

theorem presentationHNFSmoke :
    (hermiteNormalFormFin presentationMatrixZ).H =
      presentationHNFMatrixZ := by
  simpa [presentationHNFCertificateZ] using hnfEqOfLeftCertificateInt
    (hermiteNormalFormFin presentationMatrixZ)
    presentationHNFCertificateZ
    presentationHNFSpec

theorem zeroMatrixHNFExists :
    ∃ result : HNFResult zeroMatrixZ, hermiteNormalForm zeroMatrixZ = result :=
  ⟨hermiteNormalForm zeroMatrixZ, rfl⟩

theorem fullRankHNFExists :
    ∃ result : HNFResult fullRankMatrixZ, hermiteNormalForm fullRankMatrixZ = result :=
  ⟨hermiteNormalForm fullRankMatrixZ, rfl⟩

theorem rankDeficientHNFExists :
    ∃ result : HNFResult rankDeficientMatrixZ,
      hermiteNormalForm rankDeficientMatrixZ = result :=
  ⟨hermiteNormalForm rankDeficientMatrixZ, rfl⟩

theorem unitBoundaryHNFExists :
    ∃ result : HNFResult unitBoundaryMatrixZ, hermiteNormalForm unitBoundaryMatrixZ = result :=
  ⟨hermiteNormalForm unitBoundaryMatrixZ, rfl⟩

theorem polynomialMatrixQXHNFExists
    [NormalForms.ComputableEuclideanOps (Polynomial Rat)] :
    ∃ result : HNFResult polynomialMatrixQX, hermiteNormalForm polynomialMatrixQX = result :=
  ⟨hermiteNormalForm polynomialMatrixQX, rfl⟩

theorem fullRankHNFPublicSmoke :
    hermiteNormalForm fullRankMatrixZ = fullRankHNFPublic :=
  rfl

theorem fullRankHNFPublicLeftMulSmoke :
    fullRankHNFPublic.U * fullRankMatrixZ = fullRankHNFPublic.H :=
  fullRankHNFPublic.equation

theorem fullRankHNFPublicIsHermiteSmoke :
    IsHermiteNormalFormWith fullRankHNFPublic.indexing fullRankHNFPublic.H :=
  fullRankHNFPublic.isHermite

theorem fullRankHNFPublicUniqueSmoke :
    fullRankHNFPublic.H = fullRankHNFPublic.H := by
  exact isHermiteNormalFormWith_unique_of_left_equiv
    fullRankHNFPublic.indexing
    fullRankHNFPublicIsHermiteSmoke
    fullRankHNFPublicIsHermiteSmoke
    (U := 1)
    unimodular_one
    (by simp)

theorem fullRankHNFPublicUnimodularSmoke :
    Unimodular fullRankHNFPublic.U :=
  fullRankHNFPublic.U_cert.unimodular

theorem fullRankHNFPublicCertificateSmoke :
    (fullRankHNFPublic.toCertificate).U * fullRankMatrixZ =
      (fullRankHNFPublic.toCertificate).result := by
  exact (fullRankHNFPublic.toCertificate).equation

theorem fullRankHNFPublicCertificateMatchesResult :
    (fullRankHNFPublic.toCertificate).result = fullRankHNFPublic.H := by
  rfl

theorem fullRankSNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag fullRankSNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [fullRankSNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, fullRankSNFMatrixZ]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, fullRankSNFMatrixZ]

theorem rankDeficientSNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag rankDeficientSNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rankDeficientSNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, rankDeficientSNFMatrixZ]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, rankDeficientSNFMatrixZ]

theorem unitBoundarySNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag unitBoundarySNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [unitBoundarySNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [NormalForms.Matrix.Smith.Internal.diagEntry, unitBoundarySNFMatrixZ,
        Int.normalize_of_nonneg]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, unitBoundarySNFMatrixZ]

theorem presentationSNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag presentationSNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [presentationSNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [NormalForms.Matrix.Smith.Internal.diagEntry, presentationSNFMatrixZ,
        Int.normalize_of_nonneg]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, presentationSNFMatrixZ]

theorem simpleSmithMatrixQXSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag simpleSmithMatrixQX := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [simpleSmithMatrixQX] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [NormalForms.Matrix.Smith.Internal.diagEntry, simpleSmithMatrixQX]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp [NormalForms.Matrix.Smith.Internal.diagEntry, simpleSmithMatrixQX]

theorem zeroMatrixSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors zeroMatrixZ = [] := by
  rfl

theorem fullRankSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors fullRankSNFMatrixZ = [1, 1] := by
  rfl

theorem rankDeficientSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors rankDeficientSNFMatrixZ = [1] := by
  rfl

theorem unitBoundarySNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors unitBoundarySNFMatrixZ = [1, 2] := by
  rfl

theorem presentationSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors presentationSNFMatrixZ = [2, 2] := by
  rfl

theorem simpleSmithMatrixQXInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors simpleSmithMatrixQX = [1, 1] := by
  simp [NormalForms.Matrix.Smith.Internal.invariantFactors, simpleSmithMatrixQX, lowerRight]

theorem zeroMatrixSNFSmoke :
    (smithNormalFormFin zeroMatrixZ).S = zeroMatrixZ := by
  rfl


theorem fullRankSNFSmoke :
    (smithNormalFormFin fullRankMatrixZ).S =
      fullRankSNFMatrixZ := by
  let cert : TwoSidedCertificate fullRankMatrixZ :=
    { U := fullRankSNFLeftZ
      U_cert := fullRankSNFLeftInverseCertificate
      result := fullRankSNFMatrixZ
      V := 1
      V_cert := MatrixInverseCertificate.one
      equation := by decide }
  simpa [cert] using snfEqOfCertificateInt
    (smithNormalFormFin fullRankMatrixZ)
    cert
    (NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin fullRankSNFSpecSmoke)


theorem rankDeficientSNFSmoke :
    (smithNormalFormFin rankDeficientMatrixZ).S =
      rankDeficientSNFMatrixZ := by
  let cert : TwoSidedCertificate rankDeficientMatrixZ :=
    { U := rankDeficientSNFLeftZ
      U_cert := rankDeficientSNFLeftInverseCertificate
      result := rankDeficientSNFMatrixZ
      V := rankDeficientSNFRightZ
      V_cert := rankDeficientSNFRightInverseCertificate
      equation := by decide }
  simpa [cert] using snfEqOfCertificateInt
    (smithNormalFormFin rankDeficientMatrixZ)
    cert
    (NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin rankDeficientSNFSpecSmoke)


theorem unitBoundarySNFSmoke :
    (smithNormalFormFin unitBoundaryMatrixZ).S =
      unitBoundarySNFMatrixZ := by
  let cert : TwoSidedCertificate unitBoundaryMatrixZ :=
    { U := rowOperationMatrix (.smul (0 : Fin 2) (-1))
      U_cert := unitBoundaryRowOpInverseCertificate
      result := unitBoundarySNFMatrixZ
      V := 1
      V_cert := MatrixInverseCertificate.one
      equation := by decide }
  simpa [cert] using snfEqOfCertificateInt
    (smithNormalFormFin unitBoundaryMatrixZ)
    cert
    (NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin unitBoundarySNFSpecSmoke)


theorem presentationSNFSmoke :
    (smithNormalFormFin presentationMatrixZ).S =
      presentationSNFMatrixZ := by
  let cert : TwoSidedCertificate presentationMatrixZ :=
    { U := 1
      U_cert := MatrixInverseCertificate.one
      result := presentationSNFMatrixZ
      V := presentationSNFRightZ
      V_cert := presentationSNFRightInverseCertificate
      equation := by decide }
  simpa [cert] using snfEqOfCertificateInt
    (smithNormalFormFin presentationMatrixZ)
    cert
    (NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin presentationSNFSpecSmoke)


theorem prepareLeadColumnStepDataTopLeftSmoke :
    (NormalForms.Matrix.Smith.Internal.prepareLeadColumnStepData
      (A := prepareLeadColumnMatrixZ)
      (TwoSidedTransform.refl prepareLeadColumnMatrixZ) (0 : Fin 1)).B 0 0 =
      (ComputableEuclideanOps.xgcd (6 : Int) 15).gcd := by
  have hwit :
      (TwoSidedTransform.refl prepareLeadColumnMatrixZ).B (0 : Fin 1).succ 0 ≠ 0 := by
    norm_num [prepareLeadColumnMatrixZ, TwoSidedTransform.refl]
  simpa [prepareLeadColumnMatrixZ, TwoSidedTransform.refl] using
    NormalForms.Matrix.Smith.Internal.prepareLeadColumnStepData_topLeft_eq_xgcd
      (t := TwoSidedTransform.refl prepareLeadColumnMatrixZ) (i := (0 : Fin 1)) hwit

theorem prepareLeadRowStepDataTopLeftSmoke :
    (NormalForms.Matrix.Smith.Internal.prepareLeadRowStepData
      (A := prepareLeadRowMatrixZ)
      (TwoSidedTransform.refl prepareLeadRowMatrixZ) (0 : Fin 1)).B 0 0 =
      (ComputableEuclideanOps.xgcd (6 : Int) 15).gcd := by
  have hwit :
      (TwoSidedTransform.refl prepareLeadRowMatrixZ).B 0 (0 : Fin 1).succ ≠ 0 := by
    norm_num [prepareLeadRowMatrixZ, TwoSidedTransform.refl]
  simpa [prepareLeadRowMatrixZ, TwoSidedTransform.refl] using
    NormalForms.Matrix.Smith.Internal.prepareLeadRowStepData_topLeft_eq_xgcd
      (t := TwoSidedTransform.refl prepareLeadRowMatrixZ) (j := (0 : Fin 1)) hwit

theorem improvePivotStepDataSmoke :
    let t :=
      NormalForms.Matrix.Smith.Internal.improvePivotStepData
        improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2)
    t.B 0 0 = 3 ∧ t.B 0 0 ≠ 0 ∧
      Int.natAbs (t.B 0 0) < Int.natAbs (improvePivotMatrixZ 0 0) := by
  dsimp
  have hbad :
      ¬ improvePivotLeadClearedStateZ.t.B 0 0 ∣
        improvePivotLeadClearedStateZ.t.B (0 : Fin 2).succ (1 : Fin 2).succ := by
    change ¬ (6 : Int) ∣ 15
    norm_num
  have htop :
      (NormalForms.Matrix.Smith.Internal.improvePivotStepData
        improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2)).B 0 0 = 3 := by
    have htop' :=
      NormalForms.Matrix.Smith.Internal.improvePivot_topLeft_eq_xgcd
        improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2) hbad
    have hxgcd : (ComputableEuclideanOps.xgcd (6 : Int) 15).gcd = 3 := by
      decide
    simpa [improvePivotLeadClearedStateZ, improvePivotMatrixZ,
      TwoSidedTransform.refl] using htop'.trans hxgcd
  refine ⟨htop, ?_, ?_⟩
  · rw [htop]
    norm_num
  · norm_num [htop, improvePivotMatrixZ]

theorem stabilizePivotColumnWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstCol? prepareLeadColumnMatrixZ =
      some (0 : Fin 1) := by
  rfl

theorem stabilizePivotRowWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstRow? prepareLeadRowMatrixZ =
      some (0 : Fin 1) := by
  rfl

theorem stabilizePivotImproveWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleLowerRight? improvePivotMatrixZ (6 : Int) =
      some ((0 : Fin 2), (1 : Fin 2)) := by
  rfl

theorem stabilizePivotAlreadyDivisibleWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstCol? fullRankSNFMatrixZ = none ∧
      NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstRow? fullRankSNFMatrixZ = none ∧
      NormalForms.Matrix.Smith.Internal.firstUndivisibleLowerRight? fullRankSNFMatrixZ (1 : Int) =
        none := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

theorem stabilizePivotColumnResultSmoke :
    (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadColumnPivotStateZ).t.B
      (0 : Fin 1).succ 0 = 0 := by
  exact (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadColumnPivotStateZ).colCleared _

theorem stabilizePivotRowResultSmoke :
    (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadRowPivotStateZ).t.B
      0 (0 : Fin 1).succ = 0 := by
  exact (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadRowPivotStateZ).rowCleared _

noncomputable abbrev improvePivotStabilizedZ :
    NormalForms.Matrix.Smith.Internal.PivotDivisibleState improvePivotMatrixZ :=
  NormalForms.Matrix.Smith.Internal.stabilizePivot improvePivotLeadClearedStateZ.toPivotState

theorem stabilizePivotImproveResultSmoke :
    improvePivotStabilizedZ.t.B 0 0 ∣
      improvePivotStabilizedZ.t.B
        (0 : Fin 2).succ (0 : Fin 2).succ := by
  exact improvePivotStabilizedZ.lowerRightDivisible _ _

theorem stabilizePivotAlreadyDivisibleResultSmoke :
    (NormalForms.Matrix.Smith.Internal.stabilizePivot fullRankSNFPivotStateZ).t.B 0 0 ∣
      (NormalForms.Matrix.Smith.Internal.stabilizePivot fullRankSNFPivotStateZ).t.B
        (0 : Fin 1).succ (0 : Fin 1).succ := by
  let result := NormalForms.Matrix.Smith.Internal.stabilizePivot fullRankSNFPivotStateZ
  exact result.lowerRightDivisible _ _

def fullRankSNFCertificateZ : TwoSidedCertificate fullRankMatrixZ :=
  { U := fullRankSNFLeftZ
    U_cert := fullRankSNFLeftInverseCertificate
    result := fullRankSNFMatrixZ
    V := 1
    V_cert := MatrixInverseCertificate.one
    equation := by decide }

def rankDeficientSNFCertificateZ : TwoSidedCertificate rankDeficientMatrixZ :=
  { U := rankDeficientSNFLeftZ
    U_cert := rankDeficientSNFLeftInverseCertificate
    result := rankDeficientSNFMatrixZ
    V := rankDeficientSNFRightZ
    V_cert := rankDeficientSNFRightInverseCertificate
    equation := by decide }

def unitBoundarySNFCertificateZ : TwoSidedCertificate unitBoundaryMatrixZ :=
  { U := rowOperationMatrix (.smul (0 : Fin 2) (-1))
    U_cert := unitBoundaryRowOpInverseCertificate
    result := unitBoundarySNFMatrixZ
    V := 1
    V_cert := MatrixInverseCertificate.one
    equation := by decide }

def presentationSNFCertificateZ : TwoSidedCertificate presentationMatrixZ :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    result := presentationSNFMatrixZ
    V := presentationSNFRightZ
    V_cert := presentationSNFRightInverseCertificate
    equation := by decide }

theorem fullRankSNFCertificateSmoke :
    fullRankSNFCertificateZ.U * fullRankMatrixZ * fullRankSNFCertificateZ.V =
      fullRankSNFCertificateZ.result := by
  exact fullRankSNFCertificateZ.equation

theorem rankDeficientSNFCertificateSmoke :
    rankDeficientSNFCertificateZ.U * rankDeficientMatrixZ * rankDeficientSNFCertificateZ.V =
      rankDeficientSNFCertificateZ.result := by
  exact rankDeficientSNFCertificateZ.equation

theorem unitBoundarySNFCertificateSmoke :
    unitBoundarySNFCertificateZ.U * unitBoundaryMatrixZ * unitBoundarySNFCertificateZ.V =
      unitBoundarySNFCertificateZ.result := by
  exact unitBoundarySNFCertificateZ.equation

theorem presentationSNFCertificateSmoke :
    presentationSNFCertificateZ.U * presentationMatrixZ * presentationSNFCertificateZ.V =
      presentationSNFCertificateZ.result := by
  exact presentationSNFCertificateZ.equation

theorem fullRankSNFCertificateLeftInverseSmoke :
    fullRankSNFCertificateZ.U_cert.inverse * fullRankSNFCertificateZ.U = 1 :=
  fullRankSNFCertificateZ.U_cert.left_inv

theorem fullRankSNFCertificateRightInverseSmoke :
    fullRankSNFCertificateZ.U * fullRankSNFCertificateZ.U_cert.inverse = 1 :=
  fullRankSNFCertificateZ.U_cert.right_inv

noncomputable def simpleSmithSNFCertificateQX :
    TwoSidedCertificate simpleSmithMatrixQX :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    result := simpleSmithMatrixQX
    V := 1
    V_cert := MatrixInverseCertificate.one
    equation := by simp }

theorem simpleSmithSNFCertificateQXSmoke :
    simpleSmithSNFCertificateQX.U * simpleSmithMatrixQX * simpleSmithSNFCertificateQX.V =
      simpleSmithSNFCertificateQX.result := by
  exact simpleSmithSNFCertificateQX.equation

noncomputable def fullRankSNFPublic : SNFResult fullRankMatrixZ :=
  smithNormalForm fullRankMatrixZ
noncomputable def rankDeficientSNFPublic : SNFResult rankDeficientMatrixZ :=
  smithNormalForm rankDeficientMatrixZ

noncomputable def unitBoundarySNFPublic : SNFResult unitBoundaryMatrixZ :=
  smithNormalForm unitBoundaryMatrixZ

noncomputable def presentationSNFPublic : SNFResult presentationMatrixZ :=
  smithNormalForm presentationMatrixZ

noncomputable def polynomialMatrixQXSNFPublic
    [NormalForms.ComputableEuclideanOps (Polynomial Rat)] :
    SNFResult polynomialMatrixQX :=
  smithNormalForm polynomialMatrixQX



theorem zeroMatrixSNFExists :
    ∃ result : SNFResult zeroMatrixZ, smithNormalForm zeroMatrixZ = result :=
  ⟨smithNormalForm zeroMatrixZ, rfl⟩


theorem fullRankSNFExists :
    ∃ result : SNFResult fullRankMatrixZ, smithNormalForm fullRankMatrixZ = result :=
  ⟨smithNormalForm fullRankMatrixZ, rfl⟩


theorem rankDeficientSNFExists :
    ∃ result : SNFResult rankDeficientMatrixZ, smithNormalForm rankDeficientMatrixZ = result :=
  ⟨smithNormalForm rankDeficientMatrixZ, rfl⟩


theorem unitBoundarySNFExists :
    ∃ result : SNFResult unitBoundaryMatrixZ, smithNormalForm unitBoundaryMatrixZ = result :=
  ⟨smithNormalForm unitBoundaryMatrixZ, rfl⟩


theorem presentationSNFExists :
    ∃ result : SNFResult presentationMatrixZ, smithNormalForm presentationMatrixZ = result :=
  ⟨smithNormalForm presentationMatrixZ, rfl⟩


theorem polynomialMatrixQXSNFExists
    [NormalForms.ComputableEuclideanOps (Polynomial Rat)] :
    ∃ result : SNFResult polynomialMatrixQX, smithNormalForm polynomialMatrixQX = result :=
  ⟨smithNormalForm polynomialMatrixQX, rfl⟩


theorem fullRankSNFPublicSmoke :
    smithNormalForm fullRankMatrixZ = fullRankSNFPublic :=
  rfl


theorem fullRankSNFPublicEquationSmoke :
    fullRankSNFPublic.U * fullRankMatrixZ * fullRankSNFPublic.V = fullRankSNFPublic.S :=
  fullRankSNFPublic.equation


theorem fullRankSNFPublicIsSmithSmoke :
    IsSmithNormalFormWith fullRankSNFPublic.indexing fullRankSNFPublic.S :=
  fullRankSNFPublic.isSmith


theorem fullRankSNFPublicLeftUnimodularSmoke :
    Unimodular fullRankSNFPublic.U :=
  fullRankSNFPublic.U_cert.unimodular


theorem fullRankSNFPublicRightUnimodularSmoke :
    Unimodular fullRankSNFPublic.V :=
  fullRankSNFPublic.V_cert.unimodular

theorem rankDeficientSNFPublicSmoke :
    smithNormalForm rankDeficientMatrixZ = rankDeficientSNFPublic :=
  rfl

theorem unitBoundarySNFPublicSmoke :
    smithNormalForm unitBoundaryMatrixZ = unitBoundarySNFPublic :=
  rfl

theorem presentationSNFPublicSmoke :
    smithNormalForm presentationMatrixZ = presentationSNFPublic :=
  rfl

theorem polynomialMatrixQXSNFPublicSmoke
    [NormalForms.ComputableEuclideanOps (Polynomial Rat)] :
    smithNormalForm polynomialMatrixQX = polynomialMatrixQXSNFPublic :=
  rfl

theorem fullRankPidSmithCoeffListSmoke :
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList fullRankMatrixZ =
      fullRankSNFPublic.invariantFactors := by
  simpa only [fullRankSNFPublic] using
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList_eq_resultInvariantFactors
      fullRankMatrixZ

theorem rankDeficientPidSmithCoeffListSmoke :
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList rankDeficientMatrixZ =
      rankDeficientSNFPublic.invariantFactors := by
  simpa only [rankDeficientSNFPublic] using
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList_eq_resultInvariantFactors
      rankDeficientMatrixZ

theorem unitBoundaryPidSmithCoeffListSmoke :
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList unitBoundaryMatrixZ =
      unitBoundarySNFPublic.invariantFactors := by
  simpa only [unitBoundarySNFPublic] using
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList_eq_resultInvariantFactors
      unitBoundaryMatrixZ

theorem presentationPidSmithCoeffListSmoke :
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList presentationMatrixZ =
      presentationSNFPublic.invariantFactors := by
  simpa only [presentationSNFPublic] using
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList_eq_resultInvariantFactors
      presentationMatrixZ

theorem polynomialMatrixQXPidSmithCoeffListSmoke
    [NormalForms.ComputableEuclideanOps (Polynomial Rat)] :
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList polynomialMatrixQX =
      polynomialMatrixQXSNFPublic.invariantFactors := by
  simpa only [polynomialMatrixQXSNFPublic] using
    NormalForms.Bridge.MathlibPID.pidSmithNormalFormCoeffList_eq_resultInvariantFactors
      polynomialMatrixQX


theorem fullRankRowSwapSmoke :
    applyRowOperation fullRankMatrixZ (.swap (0 : Fin 2) (1 : Fin 2)) = swappedFullRankMatrixZ := by
  decide

theorem fullRankRowAddSmoke :
    applyRowOperation fullRankMatrixZ (.add (0 : Fin 2) (1 : Fin 2) 2) =
      rowAddedFullRankMatrixZ := by
  decide

theorem fullRankRowScaleSmoke :
    applyRowOperation fullRankMatrixZ (.smul (1 : Fin 2) (-1)) = rowScaledFullRankMatrixZ := by
  decide

theorem presentationColumnSwapSmoke :
    applyColumnOperation presentationMatrixZ (.swap (0 : Fin 3) (2 : Fin 3)) =
      swappedPresentationColumnsZ := by
  decide

theorem presentationColumnAddSmoke :
    applyColumnOperation presentationMatrixZ (.add (0 : Fin 3) (1 : Fin 3) (-1)) =
      addedPresentationColumnsZ := by
  decide

theorem presentationColumnScaleSmoke :
    applyColumnOperation presentationMatrixZ (.smul (2 : Fin 3) (-1)) =
      scaledPresentationColumnsZ := by
  decide

theorem mixedReplaySmoke :
    replayLog presentationMatrixZ mixedLog = mixedReplayMatrixZ := by
  decide

theorem fullRankRowSwapMatrixSmoke :
    rowOperationMatrix (.swap (0 : Fin 2) (1 : Fin 2)) * fullRankMatrixZ =
      swappedFullRankMatrixZ := by
  calc
    rowOperationMatrix (.swap (0 : Fin 2) (1 : Fin 2)) * fullRankMatrixZ
        = applyRowOperation fullRankMatrixZ (.swap (0 : Fin 2) (1 : Fin 2)) :=
          rowOperationMatrix_mul fullRankMatrixZ (.swap (0 : Fin 2) (1 : Fin 2))
    _ = swappedFullRankMatrixZ := fullRankRowSwapSmoke

theorem fullRankRowAddMatrixSmoke :
    rowOperationMatrix (.add (0 : Fin 2) (1 : Fin 2) 2) * fullRankMatrixZ =
      rowAddedFullRankMatrixZ := by
  calc
    rowOperationMatrix (.add (0 : Fin 2) (1 : Fin 2) 2) * fullRankMatrixZ
        = applyRowOperation fullRankMatrixZ (.add (0 : Fin 2) (1 : Fin 2) 2) :=
          rowOperationMatrix_mul fullRankMatrixZ (.add (0 : Fin 2) (1 : Fin 2) 2)
    _ = rowAddedFullRankMatrixZ := fullRankRowAddSmoke

theorem fullRankRowScaleMatrixSmoke :
    rowOperationMatrix (.smul (1 : Fin 2) (-1)) * fullRankMatrixZ = rowScaledFullRankMatrixZ := by
  calc
    rowOperationMatrix (.smul (1 : Fin 2) (-1)) * fullRankMatrixZ
        = applyRowOperation fullRankMatrixZ (.smul (1 : Fin 2) (-1)) :=
          rowOperationMatrix_mul fullRankMatrixZ (.smul (1 : Fin 2) (-1))
    _ = rowScaledFullRankMatrixZ := fullRankRowScaleSmoke

theorem presentationColumnSwapMatrixSmoke :
    presentationMatrixZ * columnOperationMatrix (.swap (0 : Fin 3) (2 : Fin 3)) =
      swappedPresentationColumnsZ := by
  calc
    presentationMatrixZ * columnOperationMatrix (.swap (0 : Fin 3) (2 : Fin 3))
        = applyColumnOperation presentationMatrixZ (.swap (0 : Fin 3) (2 : Fin 3)) :=
          mul_columnOperationMatrix presentationMatrixZ (.swap (0 : Fin 3) (2 : Fin 3))
    _ = swappedPresentationColumnsZ := presentationColumnSwapSmoke

theorem presentationColumnAddMatrixSmoke :
    presentationMatrixZ * columnOperationMatrix (.add (0 : Fin 3) (1 : Fin 3) (-1)) =
      addedPresentationColumnsZ := by
  calc
    presentationMatrixZ * columnOperationMatrix (.add (0 : Fin 3) (1 : Fin 3) (-1))
        = applyColumnOperation presentationMatrixZ (.add (0 : Fin 3) (1 : Fin 3) (-1)) :=
          mul_columnOperationMatrix presentationMatrixZ (.add (0 : Fin 3) (1 : Fin 3) (-1))
    _ = addedPresentationColumnsZ := presentationColumnAddSmoke

theorem presentationColumnScaleMatrixSmoke :
    presentationMatrixZ * columnOperationMatrix (.smul (2 : Fin 3) (-1)) =
      scaledPresentationColumnsZ := by
  calc
    presentationMatrixZ * columnOperationMatrix (.smul (2 : Fin 3) (-1))
        = applyColumnOperation presentationMatrixZ (.smul (2 : Fin 3) (-1)) :=
          mul_columnOperationMatrix presentationMatrixZ (.smul (2 : Fin 3) (-1))
    _ = scaledPresentationColumnsZ := presentationColumnScaleSmoke

theorem mixedReplayCertificateSmoke :
    leftAccumulator mixedLog * presentationMatrixZ * rightAccumulator mixedLog =
      mixedReplayMatrixZ := by
  calc
    leftAccumulator mixedLog * presentationMatrixZ * rightAccumulator mixedLog
        = replayLog presentationMatrixZ mixedLog := by
            exact replayLog_eq_left_right presentationMatrixZ mixedLog
    _ = mixedReplayMatrixZ := mixedReplaySmoke

theorem mixedLogCertificateSafe : mixedLog.Forall UnimodularStep := by
  simp [List.Forall, UnimodularStep, UnimodularRowOperation, UnimodularColumnOperation]

theorem rowOnlyLogIsRow : rowOnlyLog.Forall IsRowStep := by
  simp [List.Forall, IsRowStep]

theorem mixedLogLeftUnimodular :
    Unimodular (leftAccumulator mixedLog) :=
  leftAccumulator_unimodular_of_forall mixedLog mixedLogCertificateSafe

theorem mixedLogRightUnimodular :
    Unimodular (rightAccumulator mixedLog) :=
  rightAccumulator_unimodular_of_forall mixedLog mixedLogCertificateSafe

theorem mixedLogTwoSidedCertificateSmoke :
    (TwoSidedTransformEquation.ofLog (A := presentationMatrixZ) mixedLog).U *
        presentationMatrixZ *
      (TwoSidedTransformEquation.ofLog (A := presentationMatrixZ) mixedLog).V =
      (TwoSidedTransformEquation.ofLog (A := presentationMatrixZ) mixedLog).result := by
  exact (TwoSidedTransformEquation.ofLog (A := presentationMatrixZ) mixedLog).equation

theorem rowOnlyLogLeftCertificateSmoke :
    (LeftTransformEquation.ofRowLog (A := fullRankMatrixZ) rowOnlyLog rowOnlyLogIsRow).U *
        fullRankMatrixZ =
      (LeftTransformEquation.ofRowLog
        (A := fullRankMatrixZ) rowOnlyLog rowOnlyLogIsRow).result := by
  exact (LeftTransformEquation.ofRowLog
    (A := fullRankMatrixZ) rowOnlyLog rowOnlyLogIsRow).equation

theorem mixedReversibleReplaySmoke :
    NormalForms.Matrix.Certificates.ReversibleLog.replay
      presentationMatrixZ mixedReversibleLog = mixedReplayMatrixZ := by
  decide

theorem mixedReversibleLeftInverseSmoke :
    NormalForms.Matrix.Certificates.ReversibleLog.leftInverseAccumulator
        mixedReversibleLog *
      NormalForms.Matrix.Certificates.ReversibleLog.leftAccumulator
        mixedReversibleLog = 1 :=
  NormalForms.Matrix.Certificates.ReversibleLog.leftInverse_mul_accumulator
    mixedReversibleLog

theorem mixedReversibleLeftRightInverseSmoke :
    NormalForms.Matrix.Certificates.ReversibleLog.leftAccumulator
        mixedReversibleLog *
      NormalForms.Matrix.Certificates.ReversibleLog.leftInverseAccumulator
        mixedReversibleLog = 1 :=
  NormalForms.Matrix.Certificates.ReversibleLog.leftAccumulator_mul_inverse
    mixedReversibleLog

theorem mixedReversibleRightInverseSmoke :
    NormalForms.Matrix.Certificates.ReversibleLog.rightInverseAccumulator
        mixedReversibleLog *
      NormalForms.Matrix.Certificates.ReversibleLog.rightAccumulator
        mixedReversibleLog = 1 :=
  NormalForms.Matrix.Certificates.ReversibleLog.rightInverse_mul_accumulator
    mixedReversibleLog

theorem mixedReversibleRightLeftInverseSmoke :
    NormalForms.Matrix.Certificates.ReversibleLog.rightAccumulator
        mixedReversibleLog *
      NormalForms.Matrix.Certificates.ReversibleLog.rightInverseAccumulator
        mixedReversibleLog = 1 :=
  NormalForms.Matrix.Certificates.ReversibleLog.rightAccumulator_mul_inverse
    mixedReversibleLog

theorem mixedReversibleStrongCertificateSmoke :
    let cert :=
      NormalForms.Matrix.Certificates.ReversibleLog.toTwoSidedCertificate
        (A := presentationMatrixZ) mixedReversibleLog
    cert.U * presentationMatrixZ * cert.V = cert.result := by
  exact
    (NormalForms.Matrix.Certificates.ReversibleLog.toTwoSidedCertificate
      (A := presentationMatrixZ) mixedReversibleLog).equation

theorem appendedReversibleLogInverseSmoke :
    NormalForms.Matrix.Certificates.ReversibleLog.leftInverseAccumulator
        (mixedReversibleLog ++ mixedReversibleLog) *
      NormalForms.Matrix.Certificates.ReversibleLog.leftAccumulator
        (mixedReversibleLog ++ mixedReversibleLog) = 1 :=
  NormalForms.Matrix.Certificates.ReversibleLog.leftInverse_mul_accumulator
    (mixedReversibleLog ++ mixedReversibleLog)

theorem nonUnitScaleStillExecutes :
    applyRowOperation fullRankMatrixZ (.smul (0 : Fin 2) (2 : Int)) =
      !![2, 4;
         3, 5] := by
  decide

theorem nonUnitScaleNotCertificateSafe :
    ¬ UnimodularStep
      (MatrixStep.row (.smul (0 : Fin 2) (2 : Int)) : MatrixStep Int (Fin 2) (Fin 3)) := by
  simpa [UnimodularStep, UnimodularRowOperation] using (show ¬ IsUnit (2 : Int) by decide)

theorem bezoutIntSmoke :
    _root_.Matrix.mulVec (bezoutReductionMatrix (6 : Int) 15) ![6, 15] = ![3, 0] := by
  calc
    _ = ![(NormalForms.ComputableEuclideanOps.xgcd (6 : Int) 15).gcd, 0] :=
      bezoutReductionMatrix_mulVec (6 : Int) 15
    _ = ![3, 0] := by decide

theorem bezoutIntTransposeSmoke :
    _root_.Matrix.vecMul ![6, 15] (bezoutReductionMatrix (6 : Int) 15).transpose =
      ![3, 0] := by
  calc
    _ = ![(NormalForms.ComputableEuclideanOps.xgcd (6 : Int) 15).gcd, 0] := by
          exact vecMul_bezoutReductionMatrix_transpose (6 : Int) 15
    _ = ![3, 0] := by decide

theorem bezoutIntUnimodularSmoke :
    IsUnit (bezoutReductionMatrix (6 : Int) 15).det := by
  simp [det_bezoutReductionMatrix (6 : Int) 15]

theorem bezoutReversibleStepLeftInverseSmoke :
    let log :
        NormalForms.Matrix.Certificates.ReversibleLog.ReversibleOperationLog
          Int (Fin 2) (Fin 2) :=
      [NormalForms.Matrix.Certificates.ReversibleLog.ReversibleStep.rowBezoutPair
        (6 : Int) 15]
    NormalForms.Matrix.Certificates.ReversibleLog.leftInverseAccumulator log *
        NormalForms.Matrix.Certificates.ReversibleLog.leftAccumulator log = 1 := by
  intro log
  exact
    NormalForms.Matrix.Certificates.ReversibleLog.leftInverse_mul_accumulator log

theorem unitScaleReversibleStepRightInverseSmoke :
    let log :
        NormalForms.Matrix.Certificates.ReversibleLog.ReversibleOperationLog
          Int (Fin 2) (Fin 2) :=
      [NormalForms.Matrix.Certificates.ReversibleLog.ReversibleStep.rowUnitScale
        (0 : Fin 2) (normUnit (-1 : Int))]
    NormalForms.Matrix.Certificates.ReversibleLog.leftAccumulator log *
        NormalForms.Matrix.Certificates.ReversibleLog.leftInverseAccumulator log = 1 := by
  intro log
  exact
    NormalForms.Matrix.Certificates.ReversibleLog.leftAccumulator_mul_inverse log

theorem diagonalLiftLeftInverseSmoke :
    let lifted :=
      LeftTransform.diagLift improvePivotMatrixZ
        fullRankSNFLeftZ fullRankSNFLeftInverseCertificate
    lifted.U_cert.inverse * lifted.U = 1 := by
  exact
    (LeftTransform.diagLift improvePivotMatrixZ
      fullRankSNFLeftZ fullRankSNFLeftInverseCertificate).U_cert.left_inv

theorem diagonalLiftRightInverseSmoke :
    let lifted :=
      TwoSidedTransform.diagLiftRight improvePivotMatrixZ
        fullRankSNFLeftZ fullRankSNFLeftInverseCertificate
    lifted.V * lifted.V_cert.inverse = 1 := by
  exact
    (TwoSidedTransform.diagLiftRight improvePivotMatrixZ
      fullRankSNFLeftZ fullRankSNFLeftInverseCertificate).V_cert.right_inv

theorem topBezoutLiftBothInverseSmoke :
    let lifted := LeftTransform.topBezout prepareLeadColumnMatrixZ
    lifted.U_cert.inverse * lifted.U = 1 ∧
      lifted.U * lifted.U_cert.inverse = 1 := by
  exact
    ⟨(LeftTransform.topBezout prepareLeadColumnMatrixZ).U_cert.left_inv,
      (LeftTransform.topBezout prepareLeadColumnMatrixZ).U_cert.right_inv⟩

theorem bezoutPolynomialSmoke
    [NormalForms.ComputableEuclideanOps (Polynomial Rat)] :
    _root_.Matrix.mulVec
        (bezoutReductionMatrix
          ((Polynomial.X : Polynomial Rat) + 1) (Polynomial.X : Polynomial Rat))
        ![((Polynomial.X : Polynomial Rat) + 1), (Polynomial.X : Polynomial Rat)] =
      ![
        (NormalForms.ComputableEuclideanOps.xgcd
          ((Polynomial.X : Polynomial Rat) + 1) (Polynomial.X : Polynomial Rat)).gcd,
        0
      ] := by
  exact
    bezoutReductionMatrix_mulVec
      ((Polynomial.X : Polynomial Rat) + 1) (Polynomial.X : Polynomial Rat)

private def presentationColumnSpanBasisVec₁ : Fin 2 → Int :=
  ![2, 0]

private def presentationColumnSpanBasisVec₂ : Fin 2 → Int :=
  ![0, 8]

private def unitBoundaryColumnSpanBasisVec₁ : Fin 2 → Int :=
  ![1, 0]

private def unitBoundaryColumnSpanBasisVec₂ : Fin 2 → Int :=
  ![0, 2]

private def twoTorsionSubtypeEquiv {A B : Type _}
    [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (e : A ≃+ B) :
    {x : A // (2 : Int) • x = 0} ≃ {y : B // (2 : Int) • y = 0} where
  toFun x := ⟨e x, by
    let e' := e.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance)
    have hz : e' ((2 : Int) • (x : A)) = 0 := by
      simp [x.property]
    have hmap : e' ((2 : Int) • (x : A)) = (2 : Int) • e' (x : A) := by
      simp [e']
    calc
      (2 : Int) • e' (x : A) = e' ((2 : Int) • (x : A)) := hmap.symm
      _ = 0 := hz⟩
  invFun y := ⟨e.symm y, by
    let e' := e.symm.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance)
    have hz : e' ((2 : Int) • (y : B)) = 0 := by
      simp [y.property]
    have hmap : e' ((2 : Int) • (y : B)) = (2 : Int) • e' (y : B) := by
      simp [e']
    calc
      (2 : Int) • e' (y : B) = e' ((2 : Int) • (y : B)) := hmap.symm
      _ = 0 := hz⟩
  left_inv x := by simp
  right_inv y := by simp

private def twoTorsionSubtypeLinearEquiv {A B : Type _}
    [AddCommMonoid A] [AddCommMonoid B] [Module Int A] [Module Int B]
    (e : A ≃ₗ[Int] B) :
    {x : A // (2 : Int) • x = 0} ≃ {y : B // (2 : Int) • y = 0} where
  toFun x := ⟨e x, by
    calc
      (2 : Int) • e (x : A) = e ((2 : Int) • (x : A)) := (e.map_smul _ _).symm
      _ = 0 := by simp [x.property]⟩
  invFun y := ⟨e.symm y, by
    calc
      (2 : Int) • e.symm (y : B) = e.symm ((2 : Int) • (y : B)) :=
        (e.symm.map_smul _ _).symm
      _ = 0 := by simp [y.property]⟩
  left_inv x := by simp
  right_inv y := by simp

private theorem pidExecutableSmithCoeffNatAbsList_pairwise {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    (pidExecutableSmithCoeffNatAbsList A).Pairwise (· ≤ ·) := by
  simpa [pidExecutableSmithCoeffNatAbsList] using
    (List.pairwise_insertionSort (r := (· ≤ ·))
      ((pidSmithNormalFormCoeffList A).map Int.natAbs))

private theorem pidFullRankMathlibSmithCoeffNatAbsList_pairwise {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : _root_.Matrix m n Int)
    (hfull : Module.finrank Int (pidSmithColumnSpan A) = Fintype.card m) :
    (pidFullRankMathlibSmithCoeffNatAbsList A hfull).Pairwise (· ≤ ·) := by
  simpa [pidFullRankMathlibSmithCoeffNatAbsList] using
    (List.pairwise_insertionSort (r := (· ≤ ·))
      (((Finset.univ : Finset m).toList.map fun i =>
        Int.natAbs (pidFullRankSmithNormalFormCoeffs A hfull i))))

private theorem pidExecutableSmithCoeffNatAbsList_prod {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    (pidExecutableSmithCoeffNatAbsList A).prod =
      ∏ i : Fin (pidExecutableInvariantFactorCount A),
        (pidExecutableInvariantFactorFn A i).natAbs := by
  let l := pidSmithNormalFormCoeffList A
  have hsortProd :
      ((List.ofFn fun i : Fin l.length => (l.get i).natAbs).insertionSort (· ≤ ·)).prod =
        ∏ i : Fin l.length, (l.get i).natAbs := by
    calc
      ((List.ofFn fun i : Fin l.length => (l.get i).natAbs).insertionSort (· ≤ ·)).prod
          = (List.ofFn fun i : Fin l.length => (l.get i).natAbs).prod := by
              simpa [List.prod] using
                (List.perm_insertionSort (r := (· ≤ ·))
                  (List.ofFn fun i : Fin l.length => (l.get i).natAbs)).foldr_eq
                  (f := (· * ·)) (b := 1)
      _ = ∏ i : Fin l.length, (l.get i).natAbs := by
            exact Fin.prod_ofFn (fun i : Fin l.length => (l.get i).natAbs)
  convert hsortProd using 1
  · simp [l, pidExecutableSmithCoeffNatAbsList, List.ofFn_getElem_eq_map]
  · change (∏ i : Fin l.length, (l.get i).natAbs) =
        ∏ i : Fin l.length, (l.get i).natAbs
    rfl

private theorem pidFullRankMathlibSmithCoeffNatAbsList_prod {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : _root_.Matrix m n Int)
    (hfull : Module.finrank Int (pidSmithColumnSpan A) = Fintype.card m) :
    (pidFullRankMathlibSmithCoeffNatAbsList A hfull).prod =
      ∏ i : m, (pidFullRankSmithNormalFormCoeffs A hfull i).natAbs := by
  calc
    (pidFullRankMathlibSmithCoeffNatAbsList A hfull).prod
        = (((Finset.univ : Finset m).toList.map fun i =>
            Int.natAbs (pidFullRankSmithNormalFormCoeffs A hfull i)).prod) := by
              simpa [pidFullRankMathlibSmithCoeffNatAbsList, List.prod] using
                (List.perm_insertionSort (r := (· ≤ ·))
                  (((Finset.univ : Finset m).toList.map fun i =>
                    Int.natAbs (pidFullRankSmithNormalFormCoeffs A hfull i)))).foldr_eq
                  (f := (· * ·)) (b := 1)
    _ = ∏ i : m, (pidFullRankSmithNormalFormCoeffs A hfull i).natAbs := by
          exact Finset.prod_map_toList (s := (Finset.univ : Finset m))
            (f := fun i => Int.natAbs (pidFullRankSmithNormalFormCoeffs A hfull i))

private theorem pairwise_eq_one_one_of_length_two_prod_one {l : List Nat}
    (hlen : l.length = 2)
    (hsorted : l.Pairwise (· ≤ ·))
    (hprod : l.prod = 1) :
    l = [1, 1] := by
  rcases List.length_eq_two.mp hlen with ⟨a, b, rfl⟩
  haveI : IsTrans Nat (· ≤ ·) := ⟨fun _ _ _ => Nat.le_trans⟩
  have hsorted' : a ≤ b := by
    simpa using
      (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ ·)) (a := a) (b := b) (l := [])).1
        hsorted
  have hprod' : a = 1 ∧ b = 1 := by
    simpa [List.prod] using hprod
  have ha : a = 1 := hprod'.1
  have hb : b = 1 := hprod'.2
  simp [ha, hb]

private theorem pairwise_eq_one_two_of_length_two_prod_two {l : List Nat}
    (hlen : l.length = 2)
    (hsorted : l.Pairwise (· ≤ ·))
    (hprod : l.prod = 2) :
    l = [1, 2] := by
  rcases List.length_eq_two.mp hlen with ⟨a, b, rfl⟩
  haveI : IsTrans Nat (· ≤ ·) := ⟨fun _ _ _ => Nat.le_trans⟩
  have hsorted' : a ≤ b := by
    simpa using
      (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ ·)) (a := a) (b := b) (l := [])).1
        hsorted
  have hdiv : a ∣ 2 := ⟨b, by simpa [List.prod] using hprod.symm⟩
  have haLeTwo : a ≤ 2 := by
    exact Nat.le_of_dvd (by decide) hdiv
  interval_cases a
  · simp [List.prod] at hprod
  · have hb : b = 2 := by
      simpa [List.prod] using hprod
    simp [hb]
  · have hb : b = 1 := by
      simpa [List.prod] using hprod
    simp [hb] at hsorted'

private theorem pairwise_length_two_prod_four_cases {l : List Nat}
    (hlen : l.length = 2)
    (hsorted : l.Pairwise (· ≤ ·))
    (hprod : l.prod = 4) :
    l = [1, 4] ∨ l = [2, 2] := by
  rcases List.length_eq_two.mp hlen with ⟨a, b, rfl⟩
  haveI : IsTrans Nat (· ≤ ·) := ⟨fun _ _ _ => Nat.le_trans⟩
  have hsorted' : a ≤ b := by
    simpa using
      (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ ·)) (a := a) (b := b) (l := [])).1
        hsorted
  have hdiv : a ∣ 4 := ⟨b, by simpa [List.prod] using hprod.symm⟩
  have haLeFour : a ≤ 4 := by
    exact Nat.le_of_dvd (by decide) hdiv
  interval_cases a
  · simp [List.prod] at hprod
  · have hb : b = 4 := by
      simpa [List.prod] using hprod
    exact Or.inl (by simp [hb])
  · have hb : b = 2 := by
      have hmul : 2 * b = 2 * 2 := by
        simpa [List.prod, Nat.mul_assoc] using hprod
      exact Nat.eq_of_mul_eq_mul_left (by decide) hmul
    exact Or.inr (by simp [hb])
  · have : False := by
      norm_num at hdiv
    exact this.elim
  · have hb : b = 1 := by
      simpa [List.prod] using hprod
    simp [hb] at hsorted'

private theorem fin2_ofFn_pair {α : Type _} (f : Fin 2 → α) :
    List.ofFn f = [f 0, f 1] := by
  rw [List.ofFn_succ']
  simp

private theorem fin2_toList_perm :
    List.Perm ((Finset.univ : Finset (Fin 2)).toList) [0, 1] := by
  have hlen : ((Finset.univ : Finset (Fin 2)).toList).length = 2 := by
    simp
  have hnodup : ((Finset.univ : Finset (Fin 2)).toList).Nodup := Finset.nodup_toList _
  rcases List.length_eq_two.mp hlen with ⟨a, b, hab⟩
  rw [hab] at hnodup
  rw [hab]
  have habne : a ≠ b := by
    simpa [List.nodup_cons] using hnodup
  fin_cases a <;> fin_cases b
  · contradiction
  · exact List.Perm.refl _
  · simpa using List.Perm.swap 0 1 []
  · contradiction

private theorem pidFullRankMathlibSmithCoeffNatAbsList_fin2_eq_sort_pair
    {n : Type _} [Fintype n] [DecidableEq n]
    (A : _root_.Matrix (Fin 2) n Int)
    (hfull : Module.finrank Int (pidSmithColumnSpan A) = 2) :
    pidFullRankMathlibSmithCoeffNatAbsList A hfull =
      ([ (pidFullRankSmithNormalFormCoeffs A hfull 0).natAbs,
         (pidFullRankSmithNormalFormCoeffs A hfull 1).natAbs ].insertionSort (· ≤ ·)) := by
  unfold pidFullRankMathlibSmithCoeffNatAbsList
  let f : Fin 2 → Nat := fun i =>
    (pidFullRankSmithNormalFormCoeffs A hfull i).natAbs
  have hperm : List.Perm (((Finset.univ : Finset (Fin 2)).toList.map f)) [f 0, f 1] :=
    fin2_toList_perm.map f
  exact
    (((List.perm_insertionSort (r := (· ≤ ·))
      (((Finset.univ : Finset (Fin 2)).toList.map f))).trans hperm).trans
      (List.perm_insertionSort (r := (· ≤ ·)) [f 0, f 1]).symm).eq_of_pairwise'
      (List.pairwise_insertionSort (r := (· ≤ ·)) _)
      (List.pairwise_insertionSort (r := (· ≤ ·)) _)

private theorem pidExecutableSmithCoeffNatAbsList_fin2_eq_sort_pair_of_count_eq_two
    {m n : Type _} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CanonicalMod Int]
    (A : _root_.Matrix m n Int)
    (hcount : pidExecutableInvariantFactorCount A = 2) :
    pidExecutableSmithCoeffNatAbsList A =
      ([ (pidExecutableInvariantFactorFn A (Fin.cast hcount.symm 0)).natAbs,
         (pidExecutableInvariantFactorFn A (Fin.cast hcount.symm 1)).natAbs ].insertionSort
        (· ≤ ·)) := by
  unfold pidExecutableSmithCoeffNatAbsList
  rw [show List.map Int.natAbs (pidSmithNormalFormCoeffList A) =
      List.ofFn
        (fun i : Fin (pidExecutableInvariantFactorCount A) =>
          (pidExecutableInvariantFactorFn A i).natAbs) by
        rw [← List.ofFn_getElem_eq_map (pidSmithNormalFormCoeffList A) Int.natAbs]
        simp [pidExecutableInvariantFactorFn, pidExecutableInvariantFactorCount]]
  rw [List.ofFn_congr hcount]
  exact congrArg (fun l => l.insertionSort (· ≤ ·)) <|
    fin2_ofFn_pair
      (fun i : Fin 2 => (pidExecutableInvariantFactorFn A (Fin.cast hcount.symm i)).natAbs)

private theorem fin2PiZModTwoTorsionCard_eq_two_of_sort_pair_eq_one_four
    (f : Fin 2 → Nat)
    (hsort : ([f 0, f 1].insertionSort (· ≤ ·)) = [1, 4]) :
    Nat.card {x : ((i : Fin 2) → ZMod (f i)) // (2 : Int) • x = 0} = 2 := by
  by_cases h : f 0 ≤ f 1
  · have hab : f 0 = 1 ∧ f 1 = 4 := by
      simpa [h] using hsort
    rcases hab with ⟨h0, h1⟩
    have hf : f = ![1, 4] := by
      funext i
      fin_cases i <;> simp [h0, h1]
    subst f
    have e := twoTorsionSubtypeEquiv
      ((LinearEquiv.piFinTwo Int (fun i => ZMod (![1, 4] i))).toAddEquiv)
    have hcard :
      Nat.card {x : ((i : Fin 2) → ZMod (![1, 4] i)) // (2 : Int) • x = 0}
        = Nat.card {x : ZMod 1 × ZMod 4 // (2 : Int) • x = 0} := Nat.card_congr e
    have htwo :
        Nat.card {x : ((i : Fin 2) → ZMod (![1, 4] i)) // (2 : Int) • x = 0} = 2 := by
      calc
        Nat.card {x : ((i : Fin 2) → ZMod (![1, 4] i)) // (2 : Int) • x = 0}
          = Nat.card {x : ZMod 1 × ZMod 4 // (2 : Int) • x = 0} := hcard
        _ = 2 := by
              rw [Nat.card_eq_fintype_card]
              decide
    simpa [h0, h1] using htwo
  · have hab : f 1 = 1 ∧ f 0 = 4 := by
      simpa [h] using hsort
    rcases hab with ⟨h1, h0⟩
    have hf : f = ![4, 1] := by
      funext i
      fin_cases i <;> simp [h0, h1]
    subst f
    have e := twoTorsionSubtypeEquiv
      ((LinearEquiv.piFinTwo Int (fun i => ZMod (![4, 1] i))).toAddEquiv)
    have hcard :
      Nat.card {x : ((i : Fin 2) → ZMod (![4, 1] i)) // (2 : Int) • x = 0}
        = Nat.card {x : ZMod 4 × ZMod 1 // (2 : Int) • x = 0} := Nat.card_congr e
    have htwo :
        Nat.card {x : ((i : Fin 2) → ZMod (![4, 1] i)) // (2 : Int) • x = 0} = 2 := by
      calc
        Nat.card {x : ((i : Fin 2) → ZMod (![4, 1] i)) // (2 : Int) • x = 0}
          = Nat.card {x : ZMod 4 × ZMod 1 // (2 : Int) • x = 0} := hcard
        _ = 2 := by
              rw [Nat.card_eq_fintype_card]
              decide
    simpa [h0, h1] using htwo

private def fullRankMatrixZInverseCertificate :
    MatrixInverseCertificate fullRankMatrixZ :=
  { inverse := fullRankSNFLeftZ
    left_inv := by decide
    right_inv := by decide }

theorem fullRankMatrixZUnimodularSmoke :
    Unimodular fullRankMatrixZ :=
  fullRankMatrixZInverseCertificate.unimodular

theorem fullRankColumnSpanTopSmoke :
    NormalForms.Bridge.MathlibPID.pidSmithColumnSpan fullRankMatrixZ = ⊤ := by
  calc
    NormalForms.Bridge.MathlibPID.pidSmithColumnSpan fullRankMatrixZ
        = NormalForms.Bridge.MathlibPID.pidSmithColumnSpan
            (1 : _root_.Matrix (Fin 2) (Fin 2) Int) := by
              simpa [Matrix.one_mul] using
                (NormalForms.Bridge.MathlibPID.pidSmithColumnSpan_mul_right_unimodular
                  (A := (1 : _root_.Matrix (Fin 2) (Fin 2) Int))
                  (V := fullRankMatrixZ) fullRankMatrixZInverseCertificate)
    _ = ⊤ := by
          rw [NormalForms.Bridge.MathlibPID.pidSmithColumnSpan_eq_range_mulVecLin,
            Matrix.mulVecLin_one, LinearMap.range_id]

theorem fullRankColumnSpanFinrankSmoke :
    Module.finrank Int (NormalForms.Bridge.MathlibPID.pidSmithColumnSpan fullRankMatrixZ) = 2 := by
  rw [fullRankColumnSpanTopSmoke, finrank_top, Module.finrank_pi]
  decide

private theorem unitBoundaryColumnSpanFinrankSmoke :
    Module.finrank Int
      (NormalForms.Bridge.MathlibPID.pidSmithColumnSpan unitBoundaryMatrixZ) = 2 := by
  let M := NormalForms.Bridge.MathlibPID.pidSmithColumnSpan unitBoundaryMatrixZ
  let a : M := ⟨unitBoundaryColumnSpanBasisVec₁, by
    refine ⟨![-1, 0], ?_⟩
    decide⟩
  let b : M := ⟨unitBoundaryColumnSpanBasisVec₂, by
    refine ⟨![0, 1], ?_⟩
    decide⟩
  have hlin : LinearIndependent Int ![a, b] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    · have h0 := congrArg (fun x : M => ((x : Fin 2 → Int) 0)) hg
      have h0' : g 0 = 0 := by
        simpa
          [a, b, unitBoundaryColumnSpanBasisVec₁, unitBoundaryColumnSpanBasisVec₂] using h0
      simpa using h0'
    · have h1 := congrArg (fun x : M => ((x : Fin 2 → Int) 1)) hg
      have h1' : g 1 = 0 := by
        simpa
          [a, b, unitBoundaryColumnSpanBasisVec₁, unitBoundaryColumnSpanBasisVec₂] using h1
      simpa using h1'
  have hlower : 2 ≤ Module.finrank Int M := by
    simpa using hlin.fintype_card_le_finrank
  have hupper : Module.finrank Int M ≤ 2 := by
    simpa using (Submodule.finrank_le M)
  exact le_antisymm hupper hlower

private theorem presentationColumnSpanFinrankSmoke :
    Module.finrank Int
      (NormalForms.Bridge.MathlibPID.pidSmithColumnSpan presentationMatrixZ) = 2 := by
  let M := NormalForms.Bridge.MathlibPID.pidSmithColumnSpan presentationMatrixZ
  let a : M := ⟨presentationColumnSpanBasisVec₁, by
    refine ⟨![1, 0, 0], ?_⟩
    decide⟩
  let b : M := ⟨presentationColumnSpanBasisVec₂, by
    refine ⟨![-2, 1, 0], ?_⟩
    decide⟩
  have hlin : LinearIndependent Int ![a, b] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    · have h0 := congrArg (fun x : M => ((x : Fin 2 → Int) 0)) hg
      have h0' : g 0 = 0 := by
        simpa
          [a, b, presentationColumnSpanBasisVec₁, presentationColumnSpanBasisVec₂] using h0
      simpa using h0'
    · have h1 := congrArg (fun x : M => ((x : Fin 2 → Int) 1)) hg
      have h1' : g 1 = 0 := by
        simpa
          [a, b, presentationColumnSpanBasisVec₁, presentationColumnSpanBasisVec₂] using h1
      simpa using h1'
  have hlower : 2 ≤ Module.finrank Int M := by
    simpa using hlin.fintype_card_le_finrank
  have hupper : Module.finrank Int M ≤ 2 := by
    simpa using (Submodule.finrank_le M)
  exact le_antisymm hupper hlower

private noncomputable def unitBoundaryMod2 :
    (Fin 2 → Int) →ₗ[Int] ZMod 2 where
  toFun v := (v 1 : ZMod 2)
  map_add' _ _ := by simp
  map_smul' c v := by simp

set_option linter.flexible false in
private theorem unitBoundary_ker_mod2 :
    LinearMap.ker unitBoundaryMod2 = pidSmithColumnSpan unitBoundaryMatrixZ := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    rw [pidSmithColumnSpan_eq_range_mulVecLin]
    have hdiv : (2 : Int) ∣ x 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (x 1) 2).mp hx
    rcases hdiv with ⟨k, hk⟩
    refine ⟨![-x 0, k], ?_⟩
    ext i
    fin_cases i
    · change (_root_.Matrix.mulVec unitBoundaryMatrixZ ![-x 0, k]) 0 = x 0
      rw [_root_.Matrix.mulVec, Matrix.vec2_dotProduct]
      simp [unitBoundaryMatrixZ]
    · change (_root_.Matrix.mulVec unitBoundaryMatrixZ ![-x 0, k]) 1 = x 1
      rw [_root_.Matrix.mulVec, Matrix.vec2_dotProduct]
      rw [hk]
      simp [unitBoundaryMatrixZ]
  · intro hx
    rw [pidSmithColumnSpan_eq_range_mulVecLin] at hx
    rcases hx with ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    simp [unitBoundaryMod2, unitBoundaryMatrixZ]
    left
    decide

private noncomputable def unitBoundaryQuotEquivZMod2 :
    ((Fin 2 → Int) ⧸ pidSmithColumnSpan unitBoundaryMatrixZ) ≃+ ZMod 2 := by
  let p := pidSmithColumnSpan unitBoundaryMatrixZ
  have hexact : Function.Exact p.subtype unitBoundaryMod2 := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, unitBoundary_ker_mod2]
  have hsurj : Function.Surjective unitBoundaryMod2 := by
    intro z
    refine ⟨![0, z.val], ?_⟩
    simp [unitBoundaryMod2]
  exact ((Submodule.quotEquivOfEq _ _ (Submodule.range_subtype p).symm).toAddEquiv).trans
    (hexact.linearEquivOfSurjective hsurj).toAddEquiv

private theorem unitBoundaryQuotientCardSmoke :
    Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan unitBoundaryMatrixZ)) = 2 := by
  calc
    Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan unitBoundaryMatrixZ))
      = Nat.card (ZMod 2) := Nat.card_congr unitBoundaryQuotEquivZMod2.toEquiv
    _ = 2 := Nat.card_zmod 2

private noncomputable def presentationMod2Pair :
    (Fin 2 → Int) →ₗ[Int] (ZMod 2 × ZMod 2) where
  toFun v := ((v 0 : ZMod 2), (v 1 : ZMod 2))
  map_add' _ _ := by simp
  map_smul' c v := by simp

set_option linter.flexible false in
private theorem presentationSNF_ker_mod2Pair :
    LinearMap.ker presentationMod2Pair = pidSmithColumnSpan presentationSNFMatrixZ := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    simp [presentationMod2Pair] at hx
    rw [pidSmithColumnSpan_eq_range_mulVecLin]
    have hdiv0 : (2 : Int) ∣ x 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (x 0) 2).mp hx.1
    have hdiv1 : (2 : Int) ∣ x 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (x 1) 2).mp hx.2
    rcases hdiv0 with ⟨a, ha⟩
    rcases hdiv1 with ⟨b, hb⟩
    refine ⟨![a, b, 0], ?_⟩
    ext i
    fin_cases i
    · change (_root_.Matrix.mulVec presentationSNFMatrixZ ![a, b, 0]) 0 = x 0
      rw [_root_.Matrix.mulVec, Matrix.vec3_dotProduct]
      rw [ha]
      simp [presentationSNFMatrixZ]
    · change (_root_.Matrix.mulVec presentationSNFMatrixZ ![a, b, 0]) 1 = x 1
      rw [_root_.Matrix.mulVec, Matrix.vec3_dotProduct]
      rw [hb]
      simp [presentationSNFMatrixZ]
  · intro hx
    rw [pidSmithColumnSpan_eq_range_mulVecLin] at hx
    rcases hx with ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    rw [Prod.ext_iff]
    constructor
    · simp [presentationMod2Pair, presentationSNFMatrixZ]
      left
      decide
    · simp [presentationMod2Pair, presentationSNFMatrixZ]
      left
      decide

private theorem presentationColumnSpan_eq_snf :
    pidSmithColumnSpan presentationMatrixZ = pidSmithColumnSpan presentationSNFMatrixZ := by
  calc
    pidSmithColumnSpan presentationMatrixZ
      = pidSmithColumnSpan (presentationMatrixZ * presentationSNFRightZ) := by
          simpa using
            (pidSmithColumnSpan_mul_right_unimodular (A := presentationMatrixZ)
              (V := presentationSNFRightZ) presentationSNFRightInverseCertificate).symm
    _ = pidSmithColumnSpan presentationSNFMatrixZ := by
          have hEq : presentationMatrixZ * presentationSNFRightZ = presentationSNFMatrixZ := by
            simpa [presentationSNFCertificateZ] using presentationSNFCertificateSmoke
          rw [hEq]

private noncomputable def presentationQuotEquivZMod2Prod :
    ((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ) ≃+
      (ZMod 2 × ZMod 2) := by
  let p := pidSmithColumnSpan presentationSNFMatrixZ
  have hexact : Function.Exact p.subtype presentationMod2Pair := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, presentationSNF_ker_mod2Pair]
  have hsurj : Function.Surjective presentationMod2Pair := by
    rintro ⟨a, b⟩
    refine ⟨![a.val, b.val], ?_⟩
    rw [Prod.ext_iff]
    constructor <;> simp [presentationMod2Pair]
  exact ((Submodule.quotEquivOfEq _ _ presentationColumnSpan_eq_snf).toAddEquiv).trans <|
    (((Submodule.quotEquivOfEq _ _ (Submodule.range_subtype p).symm).toAddEquiv).trans
      (hexact.linearEquivOfSurjective hsurj).toAddEquiv)

private theorem presentationQuotientCardSmoke :
    Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ)) = 4 := by
  calc
    Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ))
      = Nat.card (ZMod 2 × ZMod 2) := Nat.card_congr presentationQuotEquivZMod2Prod.toEquiv
    _ = 4 := by
          rw [Nat.card_eq_fintype_card]
          decide

private theorem presentationQuotientTwoTorsionCardSmoke :
    Nat.card
      {x : ((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ) // (2 : Int) • x = 0} = 4 := by
  let e := twoTorsionSubtypeEquiv presentationQuotEquivZMod2Prod
  calc
    Nat.card
      {x : ((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ) // (2 : Int) • x = 0}
      = Nat.card {x : ZMod 2 × ZMod 2 // (2 : Int) • x = 0} := Nat.card_congr e
    _ = 4 := by
          rw [Nat.card_eq_fintype_card]
          decide

theorem fullRankPidExecutableInvariantFactorCountSmoke :
    NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount fullRankMatrixZ = 2 := by
  exact
    NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount_eq_card_rows_of_finrank_eq_card
      fullRankMatrixZ fullRankColumnSpanFinrankSmoke

theorem presentationPidExecutableInvariantFactorCountSmoke :
    NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount presentationMatrixZ = 2 := by
  exact
    NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount_eq_card_rows_of_finrank_eq_card
      presentationMatrixZ presentationColumnSpanFinrankSmoke

theorem unitBoundaryPidExecutableInvariantFactorCountSmoke :
    NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount unitBoundaryMatrixZ = 2 := by
  exact
    NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount_eq_card_rows_of_finrank_eq_card
      unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke

theorem fullRankPidMathlibCoeffNatAbsListSmoke :
    pidFullRankMathlibSmithCoeffNatAbsList
        fullRankMatrixZ fullRankColumnSpanFinrankSmoke =
      [1, 1] := by
  have hsorted :=
    pidFullRankMathlibSmithCoeffNatAbsList_pairwise
      fullRankMatrixZ fullRankColumnSpanFinrankSmoke
  have hlen :
      (pidFullRankMathlibSmithCoeffNatAbsList
        fullRankMatrixZ fullRankColumnSpanFinrankSmoke).length = 2 := by
    exact
      pidFullRankMathlibSmithCoeffNatAbsList_length
        fullRankMatrixZ fullRankColumnSpanFinrankSmoke
  have hfull' :
      Module.finrank Int (pidSmithColumnSpan fullRankMatrixZ) =
        Module.finrank Int (Fin 2 → Int) := by
    simpa [Module.finrank_eq_card_basis (Pi.basisFun Int (Fin 2))] using
      fullRankColumnSpanFinrankSmoke
  have hprod :
      (pidFullRankMathlibSmithCoeffNatAbsList
        fullRankMatrixZ fullRankColumnSpanFinrankSmoke).prod = 1 := by
    calc
      (pidFullRankMathlibSmithCoeffNatAbsList
          fullRankMatrixZ fullRankColumnSpanFinrankSmoke).prod
          = ∏ i : Fin 2,
              (pidFullRankSmithNormalFormCoeffs
                fullRankMatrixZ fullRankColumnSpanFinrankSmoke i).natAbs :=
            pidFullRankMathlibSmithCoeffNatAbsList_prod
              fullRankMatrixZ fullRankColumnSpanFinrankSmoke
      _ = Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan fullRankMatrixZ)) := by
            let hcard :=
              Nat.card_congr
                (((pidSmithColumnSpan fullRankMatrixZ).quotientEquivPiZMod
                  (Pi.basisFun Int (Fin 2)) hfull').toEquiv)
            simpa [Nat.card_pi, Nat.card_zmod, pidFullRankSmithNormalFormCoeffs] using hcard.symm
      _ = 1 := by
            rw [fullRankColumnSpanTopSmoke]
            simp
  exact pairwise_eq_one_one_of_length_two_prod_one hlen hsorted hprod

theorem unitBoundaryPidMathlibCoeffNatAbsListSmoke :
    pidFullRankMathlibSmithCoeffNatAbsList
      unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke = [1, 2] := by
  have hsorted :=
    pidFullRankMathlibSmithCoeffNatAbsList_pairwise
      unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke
  have hlen :
      (pidFullRankMathlibSmithCoeffNatAbsList
        unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke).length = 2 := by
    exact
      pidFullRankMathlibSmithCoeffNatAbsList_length
        unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke
  have hfull' :
      Module.finrank Int (pidSmithColumnSpan unitBoundaryMatrixZ) =
        Module.finrank Int (Fin 2 → Int) := by
    simpa [Module.finrank_eq_card_basis (Pi.basisFun Int (Fin 2))] using
      unitBoundaryColumnSpanFinrankSmoke
  have hprod :
      (pidFullRankMathlibSmithCoeffNatAbsList
        unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke).prod = 2 := by
    calc
      (pidFullRankMathlibSmithCoeffNatAbsList
          unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke).prod
          = ∏ i : Fin 2,
              (pidFullRankSmithNormalFormCoeffs
                unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke i).natAbs :=
            pidFullRankMathlibSmithCoeffNatAbsList_prod
              unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke
      _ = Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan unitBoundaryMatrixZ)) := by
            let hcard :=
              Nat.card_congr
                (((pidSmithColumnSpan unitBoundaryMatrixZ).quotientEquivPiZMod
                  (Pi.basisFun Int (Fin 2)) hfull').toEquiv)
            simpa [Nat.card_pi, Nat.card_zmod, pidFullRankSmithNormalFormCoeffs] using hcard.symm
      _ = 2 := unitBoundaryQuotientCardSmoke
  exact pairwise_eq_one_two_of_length_two_prod_two hlen hsorted hprod

theorem presentationPidMathlibCoeffNatAbsListSmoke :
    pidFullRankMathlibSmithCoeffNatAbsList
      presentationMatrixZ presentationColumnSpanFinrankSmoke = [2, 2] := by
  let a :=
    (pidFullRankSmithNormalFormCoeffs
      presentationMatrixZ presentationColumnSpanFinrankSmoke 0).natAbs
  let b :=
    (pidFullRankSmithNormalFormCoeffs
      presentationMatrixZ presentationColumnSpanFinrankSmoke 1).natAbs
  have hnorm :
      pidFullRankMathlibSmithCoeffNatAbsList
          presentationMatrixZ presentationColumnSpanFinrankSmoke =
        ([a, b].insertionSort (· ≤ ·)) := by
    simpa [a, b] using
      pidFullRankMathlibSmithCoeffNatAbsList_fin2_eq_sort_pair
        presentationMatrixZ presentationColumnSpanFinrankSmoke
  have hsorted :=
    pidFullRankMathlibSmithCoeffNatAbsList_pairwise
      presentationMatrixZ presentationColumnSpanFinrankSmoke
  have hlen :
      (pidFullRankMathlibSmithCoeffNatAbsList
        presentationMatrixZ presentationColumnSpanFinrankSmoke).length = 2 := by
    exact
      pidFullRankMathlibSmithCoeffNatAbsList_length
        presentationMatrixZ presentationColumnSpanFinrankSmoke
  have hfull' :
      Module.finrank Int (pidSmithColumnSpan presentationMatrixZ) =
        Module.finrank Int (Fin 2 → Int) := by
    simpa [Module.finrank_eq_card_basis (Pi.basisFun Int (Fin 2))] using
      presentationColumnSpanFinrankSmoke
  have hprod :
      (pidFullRankMathlibSmithCoeffNatAbsList
        presentationMatrixZ presentationColumnSpanFinrankSmoke).prod = 4 := by
    calc
      (pidFullRankMathlibSmithCoeffNatAbsList
          presentationMatrixZ presentationColumnSpanFinrankSmoke).prod
          = ∏ i : Fin 2,
              (pidFullRankSmithNormalFormCoeffs
                presentationMatrixZ presentationColumnSpanFinrankSmoke i).natAbs :=
            pidFullRankMathlibSmithCoeffNatAbsList_prod
              presentationMatrixZ presentationColumnSpanFinrankSmoke
      _ = Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ)) := by
            let hcard :=
              Nat.card_congr
                (((pidSmithColumnSpan presentationMatrixZ).quotientEquivPiZMod
                  (Pi.basisFun Int (Fin 2)) hfull').toEquiv)
            simpa [Nat.card_pi, Nat.card_zmod, pidFullRankSmithNormalFormCoeffs] using hcard.symm
      _ = 4 := presentationQuotientCardSmoke
  rcases pairwise_length_two_prod_four_cases hlen hsorted hprod with honefour | htwotwo
  · have honefour' : ([a, b].insertionSort (· ≤ ·)) = [1, 4] := by
      rwa [hnorm] at honefour
    have hmodel2 :
        Nat.card
          {x : ((i : Fin 2) →
            ZMod ((pidFullRankSmithNormalFormCoeffs
              presentationMatrixZ presentationColumnSpanFinrankSmoke i).natAbs)) //
            (2 : Int) • x = 0} = 2 :=
      fin2PiZModTwoTorsionCard_eq_two_of_sort_pair_eq_one_four
        (fun i : Fin 2 =>
          (pidFullRankSmithNormalFormCoeffs
            presentationMatrixZ presentationColumnSpanFinrankSmoke i).natAbs)
        honefour'
    have hmodel4 :
        Nat.card
          {x : ((i : Fin 2) →
            ZMod ((pidFullRankSmithNormalFormCoeffs
              presentationMatrixZ presentationColumnSpanFinrankSmoke i).natAbs)) //
            (2 : Int) • x = 0} = 4 := by
      have e := twoTorsionSubtypeEquiv
        (((pidSmithColumnSpan presentationMatrixZ).quotientEquivPiZMod
          (Pi.basisFun Int (Fin 2)) hfull').symm)
      calc
        Nat.card
            {x : ((i : Fin 2) →
              ZMod ((pidFullRankSmithNormalFormCoeffs
                presentationMatrixZ presentationColumnSpanFinrankSmoke i).natAbs)) //
              (2 : Int) • x = 0}
          = Nat.card
              {x : ((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ) //
                (2 : Int) • x = 0} := by
                  exact Nat.card_congr
                    (twoTorsionSubtypeEquiv
                      (((pidSmithColumnSpan presentationMatrixZ).quotientEquivPiZMod
                        (Pi.basisFun Int (Fin 2)) hfull').symm))
        _ = 4 := presentationQuotientTwoTorsionCardSmoke
    have hcontra : False := by
      rw [hmodel2] at hmodel4
      norm_num at hmodel4
    exfalso
    exact hcontra
  · exact htwotwo

theorem fullRankPidExecutableCoeffNatAbsListSmoke :
    pidExecutableSmithCoeffNatAbsList fullRankMatrixZ = [1, 1] := by
  have hsorted := pidExecutableSmithCoeffNatAbsList_pairwise fullRankMatrixZ
  have hlen :
      (pidExecutableSmithCoeffNatAbsList fullRankMatrixZ).length = 2 := by
    simpa using
      pidExecutableSmithCoeffNatAbsList_length_of_finrank_eq_card
        fullRankMatrixZ fullRankColumnSpanFinrankSmoke
  have hprod : (pidExecutableSmithCoeffNatAbsList fullRankMatrixZ).prod = 1 := by
    calc
      (pidExecutableSmithCoeffNatAbsList fullRankMatrixZ).prod
          = ∏ i : Fin (pidExecutableInvariantFactorCount fullRankMatrixZ),
              (pidExecutableInvariantFactorFn fullRankMatrixZ i).natAbs :=
            pidExecutableSmithCoeffNatAbsList_prod fullRankMatrixZ
      _ = Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan fullRankMatrixZ)) := by
            let hcard :=
              Nat.card_congr
                ((pidExecutableQuotientEquivPiZMod
                  fullRankMatrixZ fullRankPidExecutableInvariantFactorCountSmoke).toEquiv)
            rw [hcard, Nat.card_pi]
            simp [Nat.card_zmod]
      _ = 1 := by
            rw [fullRankColumnSpanTopSmoke]
            simp
  exact pairwise_eq_one_one_of_length_two_prod_one hlen hsorted hprod

theorem unitBoundaryPidExecutableCoeffNatAbsListSmoke :
    pidExecutableSmithCoeffNatAbsList unitBoundaryMatrixZ = [1, 2] := by
  have hsorted := pidExecutableSmithCoeffNatAbsList_pairwise unitBoundaryMatrixZ
  have hlen :
      (pidExecutableSmithCoeffNatAbsList unitBoundaryMatrixZ).length = 2 := by
    simpa using
      pidExecutableSmithCoeffNatAbsList_length_of_finrank_eq_card
        unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke
  have hprod : (pidExecutableSmithCoeffNatAbsList unitBoundaryMatrixZ).prod = 2 := by
    calc
      (pidExecutableSmithCoeffNatAbsList unitBoundaryMatrixZ).prod
          = ∏ i : Fin (pidExecutableInvariantFactorCount unitBoundaryMatrixZ),
              (pidExecutableInvariantFactorFn unitBoundaryMatrixZ i).natAbs :=
            pidExecutableSmithCoeffNatAbsList_prod unitBoundaryMatrixZ
      _ = Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan unitBoundaryMatrixZ)) := by
            let hcard :=
              Nat.card_congr
                ((pidExecutableQuotientEquivPiZMod
                  unitBoundaryMatrixZ unitBoundaryPidExecutableInvariantFactorCountSmoke).toEquiv)
            rw [hcard, Nat.card_pi]
            simp [Nat.card_zmod]
      _ = 2 := unitBoundaryQuotientCardSmoke
  exact pairwise_eq_one_two_of_length_two_prod_two hlen hsorted hprod

theorem presentationPidExecutableCoeffNatAbsListSmoke :
    pidExecutableSmithCoeffNatAbsList presentationMatrixZ = [2, 2] := by
  let a :=
    (pidExecutableInvariantFactorFn presentationMatrixZ
      (Fin.cast presentationPidExecutableInvariantFactorCountSmoke.symm 0)).natAbs
  let b :=
    (pidExecutableInvariantFactorFn presentationMatrixZ
      (Fin.cast presentationPidExecutableInvariantFactorCountSmoke.symm 1)).natAbs
  have hnorm :
      pidExecutableSmithCoeffNatAbsList presentationMatrixZ =
        ([a, b].insertionSort (· ≤ ·)) := by
    simpa [a, b] using
      pidExecutableSmithCoeffNatAbsList_fin2_eq_sort_pair_of_count_eq_two
        presentationMatrixZ presentationPidExecutableInvariantFactorCountSmoke
  have hsorted := pidExecutableSmithCoeffNatAbsList_pairwise presentationMatrixZ
  have hlen :
      (pidExecutableSmithCoeffNatAbsList presentationMatrixZ).length = 2 := by
    simpa using
      pidExecutableSmithCoeffNatAbsList_length_of_finrank_eq_card
        presentationMatrixZ presentationColumnSpanFinrankSmoke
  have hprod : (pidExecutableSmithCoeffNatAbsList presentationMatrixZ).prod = 4 := by
    calc
      (pidExecutableSmithCoeffNatAbsList presentationMatrixZ).prod
          = ∏ i : Fin (pidExecutableInvariantFactorCount presentationMatrixZ),
              (pidExecutableInvariantFactorFn presentationMatrixZ i).natAbs :=
            pidExecutableSmithCoeffNatAbsList_prod presentationMatrixZ
      _ = Nat.card (((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ)) := by
            let hcard :=
              Nat.card_congr
                ((pidExecutableQuotientEquivPiZMod
                  presentationMatrixZ presentationPidExecutableInvariantFactorCountSmoke).toEquiv)
            rw [hcard, Nat.card_pi]
            simp [Nat.card_zmod]
      _ = 4 := presentationQuotientCardSmoke
  rcases pairwise_length_two_prod_four_cases hlen hsorted hprod with honefour | htwotwo
  · have honefour' : ([a, b].insertionSort (· ≤ ·)) = [1, 4] := by
      rwa [hnorm] at honefour
    have hmodel2 :
        Nat.card
          {x : ((i : Fin 2) →
            ZMod ((pidExecutableInvariantFactorFn presentationMatrixZ
              (Fin.cast presentationPidExecutableInvariantFactorCountSmoke.symm i)).natAbs)) //
            (2 : Int) • x = 0} = 2 :=
      fin2PiZModTwoTorsionCard_eq_two_of_sort_pair_eq_one_four
        (fun i : Fin 2 =>
          (pidExecutableInvariantFactorFn presentationMatrixZ
            (Fin.cast presentationPidExecutableInvariantFactorCountSmoke.symm i)).natAbs)
        honefour'
    have hmodel4 :
        Nat.card
          {x : ((i : Fin 2) →
            ZMod ((pidExecutableInvariantFactorFn presentationMatrixZ
              (Fin.cast presentationPidExecutableInvariantFactorCountSmoke.symm i)).natAbs)) //
            (2 : Int) • x = 0} = 4 := by
      have ebase := twoTorsionSubtypeEquiv
        ((LinearEquiv.piCongrLeft Int
          (fun i : Fin (pidExecutableInvariantFactorCount presentationMatrixZ) =>
            ZMod (pidExecutableInvariantFactorFn presentationMatrixZ i).natAbs)
          (finCongr presentationPidExecutableInvariantFactorCountSmoke.symm)).toAddEquiv)
      have equot := twoTorsionSubtypeEquiv
        ((pidExecutableQuotientEquivPiZMod
          presentationMatrixZ presentationPidExecutableInvariantFactorCountSmoke).symm)
      calc
        Nat.card
            {x : ((i : Fin 2) →
              ZMod ((pidExecutableInvariantFactorFn presentationMatrixZ
                (Fin.cast presentationPidExecutableInvariantFactorCountSmoke.symm i)).natAbs)) //
              (2 : Int) • x = 0}
          = Nat.card
              {x : ((i : Fin (pidExecutableInvariantFactorCount presentationMatrixZ)) →
                ZMod (pidExecutableInvariantFactorFn presentationMatrixZ i).natAbs) //
                (2 : Int) • x = 0} := by
                  exact Nat.card_congr
                    (twoTorsionSubtypeLinearEquiv
                      (LinearEquiv.piCongrLeft Int
                        (fun i : Fin (pidExecutableInvariantFactorCount presentationMatrixZ) =>
                          ZMod (pidExecutableInvariantFactorFn presentationMatrixZ i).natAbs)
                        (finCongr presentationPidExecutableInvariantFactorCountSmoke.symm)))
        _ = Nat.card
              {x : ((Fin 2 → Int) ⧸ pidSmithColumnSpan presentationMatrixZ) //
                (2 : Int) • x = 0} := Nat.card_congr equot
        _ = 4 := presentationQuotientTwoTorsionCardSmoke
    have hcontra : False := by
      rw [hmodel2] at hmodel4
      norm_num at hmodel4
    exfalso
    exact hcontra
  · exact htwotwo

theorem fullRankPidCoeffNatAbsListEqualitySmoke :
    pidFullRankMathlibSmithCoeffNatAbsList fullRankMatrixZ fullRankColumnSpanFinrankSmoke =
      pidExecutableSmithCoeffNatAbsList fullRankMatrixZ := by
  rw [fullRankPidMathlibCoeffNatAbsListSmoke, fullRankPidExecutableCoeffNatAbsListSmoke]

theorem unitBoundaryPidCoeffNatAbsListEqualitySmoke :
    pidFullRankMathlibSmithCoeffNatAbsList
        unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke =
      pidExecutableSmithCoeffNatAbsList unitBoundaryMatrixZ := by
  rw [unitBoundaryPidMathlibCoeffNatAbsListSmoke, unitBoundaryPidExecutableCoeffNatAbsListSmoke]

theorem presentationPidCoeffNatAbsListEqualitySmoke :
    pidFullRankMathlibSmithCoeffNatAbsList
        presentationMatrixZ presentationColumnSpanFinrankSmoke =
      pidExecutableSmithCoeffNatAbsList presentationMatrixZ := by
  rw [presentationPidMathlibCoeffNatAbsListSmoke, presentationPidExecutableCoeffNatAbsListSmoke]

theorem fullRankPidCoeffNatAbsListLengthComparisonSmoke :
    (NormalForms.Bridge.MathlibPID.pidFullRankMathlibSmithCoeffNatAbsList
      fullRankMatrixZ fullRankColumnSpanFinrankSmoke).length =
      (NormalForms.Bridge.MathlibPID.pidExecutableSmithCoeffNatAbsList fullRankMatrixZ).length := by
  rw [NormalForms.Bridge.MathlibPID.pidFullRankMathlibSmithCoeffNatAbsList_length,
    NormalForms.Bridge.MathlibPID.pidExecutableSmithCoeffNatAbsList_length_of_finrank_eq_card
      fullRankMatrixZ fullRankColumnSpanFinrankSmoke]

theorem presentationPidCoeffNatAbsListLengthComparisonSmoke :
    (NormalForms.Bridge.MathlibPID.pidFullRankMathlibSmithCoeffNatAbsList
      presentationMatrixZ presentationColumnSpanFinrankSmoke).length =
      (NormalForms.Bridge.MathlibPID.pidExecutableSmithCoeffNatAbsList
        presentationMatrixZ).length := by
  rw [NormalForms.Bridge.MathlibPID.pidFullRankMathlibSmithCoeffNatAbsList_length,
    NormalForms.Bridge.MathlibPID.pidExecutableSmithCoeffNatAbsList_length_of_finrank_eq_card
      presentationMatrixZ presentationColumnSpanFinrankSmoke]

theorem fullRankSNFPublicInvariantFactorLengthSmoke :
    fullRankSNFPublic.invariantFactors.length = 2 := by
  simpa [fullRankSNFPublic, NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount] using
    fullRankPidExecutableInvariantFactorCountSmoke

theorem presentationSNFPublicInvariantFactorLengthSmoke :
    presentationSNFPublic.invariantFactors.length = 2 := by
  simpa
    [presentationSNFPublic, NormalForms.Bridge.MathlibPID.pidExecutableInvariantFactorCount] using
    presentationPidExecutableInvariantFactorCountSmoke

noncomputable def presentationPidExecutableQuotientEquivPiCoordsSmoke :=
  NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiCoords presentationMatrixZ

noncomputable def presentationPidExecutableQuotientEquivPiSpanProdSmoke :=
  NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiSpanProd presentationMatrixZ

noncomputable def presentationPidExecutableQuotientEquivPiZModProdSmoke :=
  NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiZModProd presentationMatrixZ

noncomputable def presentationPidExecutableQuotientEquivPiSpanSmoke :=
  NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiSpan presentationMatrixZ
    presentationPidExecutableInvariantFactorCountSmoke

noncomputable def presentationPidExecutableQuotientEquivDirectSumSmoke :=
  NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivDirectSum presentationMatrixZ
    presentationPidExecutableInvariantFactorCountSmoke

noncomputable def mixedPidExecutableQuotientEquivPiSpanProdSmoke :=
  NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiSpanProd mixedTorsionFreeMatrixZ

noncomputable def mixedPidExecutableQuotientEquivPiZModProdSmoke :=
  NormalForms.Bridge.MathlibPID.pidExecutableQuotientEquivPiZModProd mixedTorsionFreeMatrixZ

noncomputable def fullRankPidFullRankMathlibQuotientEquivExecutableSmoke :=
  NormalForms.Bridge.MathlibPID.pidFullRankMathlibQuotientEquivExecutable fullRankMatrixZ
    fullRankColumnSpanFinrankSmoke fullRankPidExecutableInvariantFactorCountSmoke

noncomputable def fullRankPidFullRankMathlibDirectSumEquivExecutableSmoke :=
  NormalForms.Bridge.MathlibPID.pidFullRankMathlibDirectSumEquivExecutable fullRankMatrixZ
    fullRankColumnSpanFinrankSmoke fullRankPidExecutableInvariantFactorCountSmoke

noncomputable def fullRankPidFullRankMathlibPiZModEquivExecutableSmoke :=
  NormalForms.Bridge.MathlibPID.pidFullRankMathlibPiZModEquivExecutable fullRankMatrixZ
    fullRankColumnSpanFinrankSmoke fullRankPidExecutableInvariantFactorCountSmoke

noncomputable def unitBoundaryPidFullRankMathlibPiZModEquivExecutableSmoke :=
  NormalForms.Bridge.MathlibPID.pidFullRankMathlibPiZModEquivExecutable unitBoundaryMatrixZ
    unitBoundaryColumnSpanFinrankSmoke unitBoundaryPidExecutableInvariantFactorCountSmoke

noncomputable def presentationPidFullRankMathlibPiZModEquivExecutableSmoke :=
  NormalForms.Bridge.MathlibPID.pidFullRankMathlibPiZModEquivExecutable presentationMatrixZ
    presentationColumnSpanFinrankSmoke presentationPidExecutableInvariantFactorCountSmoke

private theorem fin2_eq_two_two_of_sorted_eq_two_two
    (f : Fin 2 → Nat)
    (hsort : ([f 0, f 1].insertionSort (· ≤ ·)) = [2, 2]) :
    f = ![2, 2] := by
  by_cases h : f 0 ≤ f 1
  · have hf : f 0 = 2 ∧ f 1 = 2 := by
      simpa [h] using hsort
    rcases hf with ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [h0, h1]
  · have hf : f 1 = 2 ∧ f 0 = 2 := by
      simpa [h] using hsort
    rcases hf with ⟨h1, h0⟩
    funext i
    fin_cases i <;> simp [h0, h1]

private theorem fin2_eq_one_two_or_two_one_of_sorted_eq_one_two
    (f : Fin 2 → Nat)
    (hsort : ([f 0, f 1].insertionSort (· ≤ ·)) = [1, 2]) :
    f = ![1, 2] ∨ f = ![2, 1] := by
  by_cases h : f 0 ≤ f 1
  · left
    have hf : f 0 = 1 ∧ f 1 = 2 := by
      simpa [h] using hsort
    rcases hf with ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [h0, h1]
  · right
    have hf : f 1 = 1 ∧ f 0 = 2 := by
      simpa [h] using hsort
    rcases hf with ⟨h1, h0⟩
    funext i
    fin_cases i <;> simp [h0, h1]

theorem presentationPublicInvariantFactorCountSmoke :
    presentationInvariantFactorCount presentationMatrixZ = 2 := by
  exact presentationInvariantFactorCount_eq_card_rows_of_finrank_eq_card_rows
    presentationMatrixZ presentationColumnSpanFinrankSmoke

theorem unitBoundaryPublicInvariantFactorCountSmoke :
    presentationInvariantFactorCount unitBoundaryMatrixZ = 2 := by
  exact presentationInvariantFactorCount_eq_card_rows_of_finrank_eq_card_rows
    unitBoundaryMatrixZ unitBoundaryColumnSpanFinrankSmoke

theorem presentationPublicInvariantFactorsSmoke :
    presentationInvariantFactors presentationMatrixZ = [2, 2] := by
  simpa [presentationInvariantFactors] using presentationPidExecutableCoeffNatAbsListSmoke

theorem unitBoundaryPublicInvariantFactorsSmoke :
    presentationInvariantFactors unitBoundaryMatrixZ = [1, 2] := by
  simpa [presentationInvariantFactors] using unitBoundaryPidExecutableCoeffNatAbsListSmoke

noncomputable def mixedTorsionFreePublicQuotientEquivPiZModProdSmoke :=
  presentationQuotientEquivPiZModProd mixedTorsionFreeMatrixZ

private noncomputable def mixedTorsionFreeMod2ProdInt :
    (Fin 2 → Int) →ₗ[Int] (ZMod 2 × Int) where
  toFun v := ((v 0 : ZMod 2), v 1)
  map_add' _ _ := by simp
  map_smul' c v := by simp

set_option linter.flexible false in
private theorem mixedTorsionFree_ker_mod2ProdInt :
    LinearMap.ker mixedTorsionFreeMod2ProdInt =
      presentationSubmodule mixedTorsionFreeMatrixZ := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, Prod.ext_iff] at hx
    rw [presentationSubmodule, pidSmithColumnSpan_eq_range_mulVecLin]
    have hdiv : (2 : Int) ∣ x 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (x 0) 2).mp hx.1
    rcases hdiv with ⟨k, hk⟩
    refine ⟨![k, 0], ?_⟩
    ext i
    fin_cases i
    · change (_root_.Matrix.mulVec mixedTorsionFreeMatrixZ ![k, 0]) 0 = x 0
      rw [_root_.Matrix.mulVec, Matrix.vec2_dotProduct]
      rw [hk]
      simp [mixedTorsionFreeMatrixZ]
    · change (_root_.Matrix.mulVec mixedTorsionFreeMatrixZ ![k, 0]) 1 = x 1
      rw [_root_.Matrix.mulVec, Matrix.vec2_dotProduct]
      have hx₂ : x 1 = 0 := by
        simpa [mixedTorsionFreeMod2ProdInt] using hx.2
      simp [mixedTorsionFreeMatrixZ, hx₂]
  · intro hx
    rw [presentationSubmodule, pidSmithColumnSpan_eq_range_mulVecLin] at hx
    rcases hx with ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Prod.ext_iff]
    constructor
    · simp [mixedTorsionFreeMod2ProdInt, mixedTorsionFreeMatrixZ]
      left
      decide
    · simp [mixedTorsionFreeMod2ProdInt, mixedTorsionFreeMatrixZ]

noncomputable def mixedTorsionFreePublicQuotientEquivZMod2IntSmoke :
    presentationQuotient mixedTorsionFreeMatrixZ ≃+ (ZMod 2 × Int) := by
  let p := presentationSubmodule mixedTorsionFreeMatrixZ
  have hexact : Function.Exact p.subtype mixedTorsionFreeMod2ProdInt := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, mixedTorsionFree_ker_mod2ProdInt]
  have hsurj : Function.Surjective mixedTorsionFreeMod2ProdInt := by
    rintro ⟨a, b⟩
    refine ⟨![a.val, b], ?_⟩
    simp [mixedTorsionFreeMod2ProdInt]
  exact ((Submodule.quotEquivOfEq _ _ (Submodule.range_subtype p).symm).toAddEquiv).trans
    (hexact.linearEquivOfSurjective hsurj).toAddEquiv

noncomputable def presentationPublicQuotientEquivZMod2ProdSmoke :
    presentationQuotient presentationMatrixZ ≃+ (ZMod 2 × ZMod 2) := by
  let eBase :=
    presentationQuotientEquivPiZMod_of_fullRank presentationMatrixZ
      presentationColumnSpanFinrankSmoke
  let f : Fin 2 → Nat := fun i =>
    presentationInvariantFactorFn presentationMatrixZ
      (Fin.cast presentationPublicInvariantFactorCountSmoke.symm i)
  let eCount :
      ((i : Fin (presentationInvariantFactorCount presentationMatrixZ)) →
          ZMod (presentationInvariantFactorFn presentationMatrixZ i)) ≃+
        ((i : Fin 2) → ZMod (f i)) :=
    (LinearEquiv.piCongrLeft Int
      (fun i : Fin (presentationInvariantFactorCount presentationMatrixZ) =>
        ZMod (presentationInvariantFactorFn presentationMatrixZ i))
      (finCongr presentationPublicInvariantFactorCountSmoke.symm)).symm.toAddEquiv
  have hpair :
      presentationInvariantFactors presentationMatrixZ =
        ([f 0, f 1].insertionSort (· ≤ ·)) := by
    simpa [presentationInvariantFactors, presentationInvariantFactorFn,
      presentationInvariantFactorCount, f] using
      pidExecutableSmithCoeffNatAbsList_fin2_eq_sort_pair_of_count_eq_two
        presentationMatrixZ presentationPublicInvariantFactorCountSmoke
  have hsort :
      ([f 0, f 1].insertionSort (· ≤ ·)) = [2, 2] := by
    rw [← hpair, presentationPublicInvariantFactorsSmoke]
  have hf : f = ![2, 2] := fin2_eq_two_two_of_sorted_eq_two_two f hsort
  have eVals : ((i : Fin 2) → ZMod (f i)) ≃+ (ZMod 2 × ZMod 2) := by
    rw [hf]
    exact (LinearEquiv.piFinTwo Int (fun i => ZMod (![2, 2] i))).toAddEquiv
  exact eBase.trans (eCount.trans eVals)

noncomputable def unitBoundaryPublicQuotientEquivZMod1ProdZMod2Smoke :
    presentationQuotient unitBoundaryMatrixZ ≃+ (ZMod 1 × ZMod 2) := by
  let eBase :=
    presentationQuotientEquivPiZMod_of_fullRank unitBoundaryMatrixZ
      unitBoundaryColumnSpanFinrankSmoke
  let f : Fin 2 → Nat := fun i =>
    presentationInvariantFactorFn unitBoundaryMatrixZ
      (Fin.cast unitBoundaryPublicInvariantFactorCountSmoke.symm i)
  let eCount :
      ((i : Fin (presentationInvariantFactorCount unitBoundaryMatrixZ)) →
          ZMod (presentationInvariantFactorFn unitBoundaryMatrixZ i)) ≃+
        ((i : Fin 2) → ZMod (f i)) :=
    (LinearEquiv.piCongrLeft Int
      (fun i : Fin (presentationInvariantFactorCount unitBoundaryMatrixZ) =>
        ZMod (presentationInvariantFactorFn unitBoundaryMatrixZ i))
      (finCongr unitBoundaryPublicInvariantFactorCountSmoke.symm)).symm.toAddEquiv
  have hpair :
      presentationInvariantFactors unitBoundaryMatrixZ =
        ([f 0, f 1].insertionSort (· ≤ ·)) := by
    simpa [presentationInvariantFactors, presentationInvariantFactorFn,
      presentationInvariantFactorCount, f] using
      pidExecutableSmithCoeffNatAbsList_fin2_eq_sort_pair_of_count_eq_two
        unitBoundaryMatrixZ unitBoundaryPublicInvariantFactorCountSmoke
  have hsort :
      ([f 0, f 1].insertionSort (· ≤ ·)) = [1, 2] := by
    rw [← hpair, unitBoundaryPublicInvariantFactorsSmoke]
  classical
  by_cases hf : f = ![1, 2]
  · have eVals : ((i : Fin 2) → ZMod (f i)) ≃+ (ZMod 1 × ZMod 2) := by
      rw [hf]
      exact (LinearEquiv.piFinTwo Int (fun i => ZMod (![1, 2] i))).toAddEquiv
    exact eBase.trans (eCount.trans eVals)
  · have hf' : f = ![2, 1] := by
      rcases fin2_eq_one_two_or_two_one_of_sorted_eq_one_two f hsort with h12 | h21
      · exact False.elim (hf h12)
      · exact h21
    have eVals : ((i : Fin 2) → ZMod (f i)) ≃+ (ZMod 1 × ZMod 2) := by
      rw [hf']
      exact ((LinearEquiv.piFinTwo Int (fun i => ZMod (![2, 1] i))).toAddEquiv).trans
        (AddEquiv.prodComm (M := ZMod 2) (N := ZMod 1))
    exact eBase.trans (eCount.trans eVals)

theorem presentationColumnSpanBridgeSmoke :
    NormalForms.Bridge.MathlibPID.pidSmithColumnSpan presentationMatrixZ =
      LinearMap.range presentationMatrixZ.mulVecLin := by
  exact NormalForms.Bridge.MathlibPID.pidSmithColumnSpan_eq_range_mulVecLin presentationMatrixZ

end NormalForms.Examples.AbelianGroups
