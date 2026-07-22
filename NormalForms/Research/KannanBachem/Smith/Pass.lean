/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.BoundedColumn
public import NormalForms.Research.KannanBachem.Hermite.PrincipalPreparation
public import NormalForms.Matrix.Smith.Defs
import all NormalForms.Matrix.Certificates.Basic

/-!
# One Kannan--Bachem Smith Pass

The 1979 Smith schedule alternates two certified Hermite phases on the active
square block:

1. put its first column into left Hermite normal form by row operations;
2. put the whole block into column Hermite normal form by applying the
   nonsingular principal-minor HNF algorithm to the transpose.

This module implements exactly that pair of phases.  Every phase returns the
existing strong `TwoSidedCertificate`; no second Smith-result type is
introduced.  Termination of the repeated pass and the outer Smith recursion
are intentionally separate proof layers.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem.Hermite

/-- The first column, represented as an `n`-by-`1` matrix. -/
@[expose] public def firstColumn {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    _root_.Matrix (Fin (n + 1)) (Fin 1) Int :=
  fun row _ => A row 0

/-- Compose two existing strong two-sided certificates. -/
@[expose] public def compose {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (first : TwoSidedCertificate A)
    (second : TwoSidedCertificate first.result) :
    TwoSidedCertificate A :=
  { U := second.U * first.U
    U_cert := second.U_cert.mul first.U_cert
    result := second.result
    V := first.V * second.V
    V_cert := first.V_cert.mul second.V_cert
    equation := by
      calc
        (second.U * first.U) * A * (first.V * second.V) =
            second.U * (first.U * A * first.V) * second.V := by
          simp only [_root_.Matrix.mul_assoc]
        _ = second.U * first.result * second.V := by
          rw [first.equation]
        _ = second.result := second.equation }

/-- Explicit inverses recover the input from any two-sided certificate. -/
public theorem inverse_equation {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (certificate : TwoSidedCertificate A) :
    certificate.U_cert.inverse * certificate.result *
        certificate.V_cert.inverse = A := by
  calc
    certificate.U_cert.inverse * certificate.result *
          certificate.V_cert.inverse =
        certificate.U_cert.inverse *
          (certificate.U * A * certificate.V) *
            certificate.V_cert.inverse := by
      rw [certificate.equation]
    _ = (certificate.U_cert.inverse * certificate.U) * A *
          (certificate.V * certificate.V_cert.inverse) := by
      simp only [_root_.Matrix.mul_assoc]
    _ = A := by
      rw [certificate.U_cert.left_inv, certificate.V_cert.right_inv,
        _root_.Matrix.one_mul, _root_.Matrix.mul_one]

/-- A two-sided invertible transform preserves nonsingularity. -/
public theorem result_det_ne_zero {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (certificate : TwoSidedCertificate A) (hdet : A.det ≠ 0) :
    certificate.result.det ≠ 0 := by
  rw [← certificate.equation, _root_.Matrix.det_mul,
    _root_.Matrix.det_mul]
  exact mul_ne_zero
    (mul_ne_zero
      (_root_.Matrix.det_ne_zero_of_left_inverse
        certificate.U_cert.left_inv)
      hdet)
    (_root_.Matrix.det_ne_zero_of_left_inverse
      certificate.V_cert.left_inv)

/-- Integer two-sided inverse certificates preserve determinant magnitude. -/
public theorem certificate_result_det_natAbs {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (certificate : TwoSidedCertificate A) :
    certificate.result.det.natAbs = A.det.natAbs := by
  rw [← certificate.equation, _root_.Matrix.det_mul,
    _root_.Matrix.det_mul, Int.natAbs_mul, Int.natAbs_mul,
    Int.isUnit_iff_natAbs_eq.mp certificate.U_cert.unimodular,
    Int.isUnit_iff_natAbs_eq.mp certificate.V_cert.unimodular]
  simp

/-- The executable one-column LHNF used by Step 4 of the Smith schedule. -/
@[expose] public def leftHermiteResult {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    HNFResultFin (firstColumn A) :=
  boundedColumnHermiteNormalForm A

/-- Apply the one-column LHNF multiplier to the entire active block. -/
@[expose] public def leftHermitePhase {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    TwoSidedCertificate A :=
  let result := leftHermiteResult A
  { U := result.U
    U_cert := result.U_cert
    result := result.U * A
    V := 1
    V_cert := MatrixInverseCertificate.one
    equation := by
      rw [_root_.Matrix.mul_one] }

/-- The phase's first column is exactly the certified one-column HNF. -/
public theorem leftHermitePhase_firstColumn {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    firstColumn (leftHermitePhase A).result = (leftHermiteResult A).H := by
  ext row column
  fin_cases column
  simpa [firstColumn, leftHermitePhase, leftHermiteResult,
    _root_.Matrix.mul_apply] using
    congrFun (congrFun (leftHermiteResult A).equation row) 0

/-- Step 4 leaves the active first column in certified HNF. -/
public theorem leftHermitePhase_isHermite {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    IsHermiteNormalFormFin (firstColumn (leftHermitePhase A).result) := by
  rw [leftHermitePhase_firstColumn]
  exact (leftHermiteResult A).isHermite

/-- The faithful nonsingular HNF computation used by Step 5 on the transpose. -/
@[expose] public def rightHermiteResult {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    HNFResultFin A.transpose :=
  Principal.preparedPrincipalHermiteNormalForm A.transpose (by
    simpa using hdet)

/-- Transpose the certified row-HNF multiplier into a right multiplier. -/
@[expose] public def rightHermitePhase {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    TwoSidedCertificate A :=
  let result := rightHermiteResult A hdet
  { U := 1
    U_cert := MatrixInverseCertificate.one
    result := result.H.transpose
    V := result.U.transpose
    V_cert := result.U_cert.transpose
    equation := by
      rw [_root_.Matrix.one_mul]
      have equation := congrArg _root_.Matrix.transpose result.equation
      simpa only [_root_.Matrix.transpose_mul,
        _root_.Matrix.transpose_transpose] using equation }

/-- Step 5 returns a certified column-Hermite matrix. -/
public theorem rightHermitePhase_transpose_isHermite {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    IsHermiteNormalFormFin (rightHermitePhase A hdet).result.transpose := by
  simpa [rightHermitePhase] using (rightHermiteResult A hdet).isHermite

/-- One complete Step-4/Step-5 pass of the Kannan--Bachem Smith schedule. -/
@[expose] public def pass {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    TwoSidedCertificate A :=
  let left := leftHermitePhase A
  let right := rightHermitePhase left.result (result_det_ne_zero left hdet)
  compose left right

public theorem pass_equation {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (pass A hdet).U * A * (pass A hdet).V = (pass A hdet).result :=
  (pass A hdet).equation

public theorem pass_inverse_equation {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (pass A hdet).U_cert.inverse * (pass A hdet).result *
        (pass A hdet).V_cert.inverse = A :=
  inverse_equation (pass A hdet)

public theorem pass_result_det_ne_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (pass A hdet).result.det ≠ 0 :=
  result_det_ne_zero (pass A hdet) hdet

/-- The final matrix of every pass is column-Hermite. -/
public theorem pass_transpose_isHermite {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    IsHermiteNormalFormFin (pass A hdet).result.transpose := by
  exact rightHermitePhase_transpose_isHermite
    (leftHermitePhase A).result
    (result_det_ne_zero (leftHermitePhase A) hdet)

end NormalForms.Research.KannanBachem.Smith
