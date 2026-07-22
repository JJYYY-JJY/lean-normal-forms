/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Matrix.Certificates.Basic

set_option linter.privateModule false

/-!
# Reversible Operation Logs

Internal operation logs whose entries carry both transformation matrices and
both inverse equations. Replay accumulates `U`, `U⁻¹`, `V`, and `V⁻¹`
constructively; no determinant or matrix inverse operation is used.
-/

namespace NormalForms.Matrix.Certificates.ReversibleLog

open scoped Matrix
open NormalForms.Matrix.Elementary

/-- A square matrix together with a chosen inverse and both inverse equations. -/
structure ReversibleMatrix (R n : Type _)
    [Fintype n] [DecidableEq n] [CommRing R] where
  forward : _root_.Matrix n n R
  backward : _root_.Matrix n n R
  backward_forward : backward * forward = 1
  forward_backward : forward * backward = 1

namespace ReversibleMatrix

def ofCertificate {R n : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    {U : _root_.Matrix n n R} (cert : MatrixInverseCertificate U) :
    ReversibleMatrix R n :=
  { forward := U
    backward := cert.inverse
    backward_forward := cert.left_inv
    forward_backward := cert.right_inv }

def certificate {R n : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (step : ReversibleMatrix R n) :
    MatrixInverseCertificate step.forward :=
  { inverse := step.backward
    left_inv := step.backward_forward
    right_inv := step.forward_backward }

end ReversibleMatrix

/-- One reversible row or column transformation. -/
inductive ReversibleStep (R m n : Type _)
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
  | row (transform : ReversibleMatrix R m)
  | col (transform : ReversibleMatrix R n)

abbrev ReversibleOperationLog (R m n : Type _)
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] :=
  List (ReversibleStep R m n)

namespace ReversibleStep

def rowSwap {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (i j : m) : ReversibleStep R m n :=
  .row (.ofCertificate (rowSwapInverseCertificate (R := R) i j))

def columnSwap {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (i j : n) : ReversibleStep R m n :=
  .col (.ofCertificate (columnSwapInverseCertificate (R := R) i j))

def rowAdd {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (src dst : m) (c : R) (hne : src ≠ dst) : ReversibleStep R m n :=
  .row (.ofCertificate (rowAddInverseCertificate src dst c hne))

def columnAdd {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (src dst : n) (c : R) (hne : src ≠ dst) : ReversibleStep R m n :=
  .col (.ofCertificate (columnAddInverseCertificate src dst c hne))

def rowUnitScale {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (i : m) (u : Rˣ) : ReversibleStep R m n :=
  .row (.ofCertificate (rowUnitScaleInverseCertificate i u))

def columnUnitScale {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (i : n) (u : Rˣ) : ReversibleStep R m n :=
  .col (.ofCertificate (columnUnitScaleInverseCertificate i u))

/-- The two-row Bézout pair primitive with its explicit 2x2 inverse. -/
def rowBezoutPair {R n : Type _}
    [Fintype n] [DecidableEq n] [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R]
    (a b : R) : ReversibleStep R (Fin 2) n :=
  .row
    { forward := bezoutReductionMatrix a b
      backward := bezoutReductionInverseMatrix a b
      backward_forward := bezoutReductionInverseMatrix_mul a b
      forward_backward := bezoutReductionMatrix_mul_inverse a b }

/-- The transposed two-column Bézout pair primitive. -/
def columnBezoutPair {R m : Type _}
    [Fintype m] [DecidableEq m] [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R]
    (a b : R) : ReversibleStep R m (Fin 2) :=
  .col <| ReversibleMatrix.ofCertificate <|
    (show MatrixInverseCertificate (bezoutReductionMatrix a b) from
      { inverse := bezoutReductionInverseMatrix a b
        left_inv := bezoutReductionInverseMatrix_mul a b
        right_inv := bezoutReductionMatrix_mul_inverse a b }).transpose

end ReversibleStep

def applyStep {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) : ReversibleStep R m n -> _root_.Matrix m n R
  | .row step => step.forward * A
  | .col step => A * step.forward

def replay {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (log : ReversibleOperationLog R m n) :
    _root_.Matrix m n R :=
  log.foldl applyStep A

def leftAccumulator {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] :
    ReversibleOperationLog R m n -> _root_.Matrix m m R
  | [] => 1
  | .row step :: log => leftAccumulator log * step.forward
  | .col _ :: log => leftAccumulator log

def leftInverseAccumulator {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] :
    ReversibleOperationLog R m n -> _root_.Matrix m m R
  | [] => 1
  | .row step :: log => step.backward * leftInverseAccumulator log
  | .col _ :: log => leftInverseAccumulator log

def rightAccumulator {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] :
    ReversibleOperationLog R m n -> _root_.Matrix n n R
  | [] => 1
  | .row _ :: log => rightAccumulator log
  | .col step :: log => step.forward * rightAccumulator log

def rightInverseAccumulator {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] :
    ReversibleOperationLog R m n -> _root_.Matrix n n R
  | [] => 1
  | .row _ :: log => rightInverseAccumulator log
  | .col step :: log => rightInverseAccumulator log * step.backward

def leftAccumulatorCertificate {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] :
    (log : ReversibleOperationLog R m n) →
      MatrixInverseCertificate (leftAccumulator log)
  | [] => MatrixInverseCertificate.one
  | .row step :: log =>
      (leftAccumulatorCertificate log).mul step.certificate
  | .col _ :: log => leftAccumulatorCertificate log

def rightAccumulatorCertificate {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] :
    (log : ReversibleOperationLog R m n) →
      MatrixInverseCertificate (rightAccumulator log)
  | [] => MatrixInverseCertificate.one
  | .row _ :: log => rightAccumulatorCertificate log
  | .col step :: log =>
      step.certificate.mul (rightAccumulatorCertificate log)

@[simp] theorem leftAccumulatorCertificate_inverse {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (log : ReversibleOperationLog R m n) :
    (leftAccumulatorCertificate log).inverse = leftInverseAccumulator log := by
  induction log with
  | nil => rfl
  | cons step log ih =>
      cases step <;> simp_all [leftAccumulatorCertificate, leftInverseAccumulator,
        MatrixInverseCertificate.mul, ReversibleMatrix.certificate]

@[simp] theorem rightAccumulatorCertificate_inverse {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (log : ReversibleOperationLog R m n) :
    (rightAccumulatorCertificate log).inverse = rightInverseAccumulator log := by
  induction log with
  | nil => rfl
  | cons step log ih =>
      cases step <;> simp_all [rightAccumulatorCertificate, rightInverseAccumulator,
        MatrixInverseCertificate.mul, ReversibleMatrix.certificate]

theorem leftInverse_mul_accumulator {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (log : ReversibleOperationLog R m n) :
    leftInverseAccumulator log * leftAccumulator log = 1 := by
  simpa using (leftAccumulatorCertificate log).left_inv

theorem leftAccumulator_mul_inverse {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (log : ReversibleOperationLog R m n) :
    leftAccumulator log * leftInverseAccumulator log = 1 := by
  simpa using (leftAccumulatorCertificate log).right_inv

theorem rightInverse_mul_accumulator {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (log : ReversibleOperationLog R m n) :
    rightInverseAccumulator log * rightAccumulator log = 1 := by
  simpa using (rightAccumulatorCertificate log).left_inv

theorem rightAccumulator_mul_inverse {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (log : ReversibleOperationLog R m n) :
    rightAccumulator log * rightInverseAccumulator log = 1 := by
  simpa using (rightAccumulatorCertificate log).right_inv

theorem replay_eq_left_right {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (log : ReversibleOperationLog R m n) :
    leftAccumulator log * A * rightAccumulator log = replay A log := by
  induction log generalizing A with
  | nil => simp [leftAccumulator, rightAccumulator, replay]
  | cons step log ih =>
      cases step with
      | row step =>
          calc
            leftAccumulator (.row step :: log) * A *
                rightAccumulator (.row step :: log) =
              leftAccumulator log * (step.forward * A) * rightAccumulator log := by
                simp [leftAccumulator, rightAccumulator, Matrix.mul_assoc]
            _ = replay (step.forward * A) log := ih _
            _ = replay A (.row step :: log) := rfl
      | col step =>
          calc
            leftAccumulator (.col step :: log) * A *
                rightAccumulator (.col step :: log) =
              leftAccumulator log * (A * step.forward) * rightAccumulator log := by
                simp [leftAccumulator, rightAccumulator, Matrix.mul_assoc]
            _ = replay (A * step.forward) log := ih _
            _ = replay A (.col step :: log) := rfl

theorem replay_append {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (first second : ReversibleOperationLog R m n) :
    replay A (first ++ second) = replay (replay A first) second := by
  induction first generalizing A with
  | nil => rfl
  | cons step log ih =>
      simp only [List.cons_append]
      change replay (applyStep A step) (log ++ second) =
        replay (replay (applyStep A step) log) second
      exact ih _

theorem leftAccumulator_append {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (first second : ReversibleOperationLog R m n) :
    leftAccumulator (first ++ second) =
      leftAccumulator second * leftAccumulator first := by
  induction first with
  | nil => simp [leftAccumulator]
  | cons step log ih =>
      cases step <;> simp [leftAccumulator, ih, Matrix.mul_assoc]

theorem rightAccumulator_append {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (first second : ReversibleOperationLog R m n) :
    rightAccumulator (first ++ second) =
      rightAccumulator first * rightAccumulator second := by
  induction first with
  | nil => simp [rightAccumulator]
  | cons step log ih =>
      cases step <;> simp [rightAccumulator, ih, Matrix.mul_assoc]

theorem leftInverseAccumulator_append {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (first second : ReversibleOperationLog R m n) :
    leftInverseAccumulator (first ++ second) =
      leftInverseAccumulator first * leftInverseAccumulator second := by
  induction first with
  | nil => simp [leftInverseAccumulator]
  | cons step log ih =>
      cases step <;> simp [leftInverseAccumulator, ih, Matrix.mul_assoc]

theorem rightInverseAccumulator_append {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (first second : ReversibleOperationLog R m n) :
    rightInverseAccumulator (first ++ second) =
      rightInverseAccumulator second * rightInverseAccumulator first := by
  induction first with
  | nil => simp [rightInverseAccumulator]
  | cons step log ih =>
      cases step <;> simp [rightInverseAccumulator, ih, Matrix.mul_assoc]

/-- Strong two-sided certificate accumulated directly from the reversible log. -/
def toTwoSidedCertificate {R m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (log : ReversibleOperationLog R m n) :
    TwoSidedCertificate A :=
  { U := leftAccumulator log
    U_cert := leftAccumulatorCertificate log
    result := replay A log
    V := rightAccumulator log
    V_cert := rightAccumulatorCertificate log
    equation := replay_eq_left_right A log }

end NormalForms.Matrix.Certificates.ReversibleLog
