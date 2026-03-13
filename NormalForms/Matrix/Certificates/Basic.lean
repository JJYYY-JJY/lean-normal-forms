import NormalForms.Matrix.Elementary

/-!
# Certificates

Reusable certificate shapes for left and two-sided normal-form transforms,
plus unimodularity lemmas for elementary steps and mixed logs.
-/

namespace NormalForms.Matrix.Certificates

open scoped Matrix

abbrev ERowOperation := NormalForms.Matrix.Elementary.RowOperation
abbrev EColumnOperation := NormalForms.Matrix.Elementary.ColumnOperation
abbrev EMatrixStep := NormalForms.Matrix.Elementary.MatrixStep
abbrev EOperationLog := NormalForms.Matrix.Elementary.OperationLog

/-- Square matrices with unit determinant. -/
def Unimodular {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (U : _root_.Matrix m m R) : Prop :=
  IsUnit U.det

structure LeftCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  result : _root_.Matrix m n R
  equation : U * A = result

structure TwoSidedCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  result : _root_.Matrix m n R
  V : _root_.Matrix n n R
  equation : U * A * V = result

@[simp] theorem unimodular_one {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R] :
    Unimodular (1 : _root_.Matrix m m R) := by
  simp [Unimodular]

@[simp] theorem unimodular_mul {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    {U V : _root_.Matrix m m R} (hU : Unimodular U) (hV : Unimodular V) :
    Unimodular (U * V) := by
  simpa [Unimodular, _root_.Matrix.det_mul] using IsUnit.mul hU hV

theorem unimodular_rowOperationMatrix {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    (op : ERowOperation R m)
    (hop : NormalForms.Matrix.Elementary.UnimodularRowOperation op) :
    Unimodular (NormalForms.Matrix.Elementary.rowOperationMatrix op) := by
  cases op with
  | swap i j =>
      simpa [Unimodular] using
        (_root_.Matrix.isUnit_det_of_left_inverse
          (A := _root_.Matrix.swap R i j)
          (B := _root_.Matrix.swap R i j)
          (_root_.Matrix.swap_mul_self (R := R) i j))
  | add src dst c =>
      simp [Unimodular, NormalForms.Matrix.Elementary.det_rowAddMatrix_of_ne src dst c hop]
  | smul i c =>
      simpa [Unimodular, NormalForms.Matrix.Elementary.rowOperationMatrix,
        NormalForms.Matrix.Elementary.det_rowScaleMatrix i c] using hop

theorem unimodular_columnOperationMatrix {n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (op : EColumnOperation R n)
    (hop : NormalForms.Matrix.Elementary.UnimodularColumnOperation op) :
    Unimodular (NormalForms.Matrix.Elementary.columnOperationMatrix op) := by
  cases op with
  | swap i j =>
      simpa [Unimodular] using
        (_root_.Matrix.isUnit_det_of_left_inverse
          (A := _root_.Matrix.swap R i j)
          (B := _root_.Matrix.swap R i j)
          (_root_.Matrix.swap_mul_self (R := R) i j))
  | add src dst c =>
      simp [Unimodular, NormalForms.Matrix.Elementary.det_columnAddMatrix_of_ne src dst c hop]
  | smul i c =>
      simpa [Unimodular, NormalForms.Matrix.Elementary.columnOperationMatrix,
        NormalForms.Matrix.Elementary.det_columnScaleMatrix i c] using hop

theorem leftAccumulator_unimodular_of_forall {m n R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    (log : EOperationLog R m n)
    (hlog : log.Forall NormalForms.Matrix.Elementary.UnimodularStep) :
    Unimodular (NormalForms.Matrix.Elementary.leftAccumulator log) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.leftAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.row op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.leftAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using
            unimodular_mul (ih hpair.2) (unimodular_rowOperationMatrix op hpair.1)
      | col op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.col op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.leftAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using ih hpair.2

theorem rightAccumulator_unimodular_of_forall {m n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (log : EOperationLog R m n)
    (hlog : log.Forall NormalForms.Matrix.Elementary.UnimodularStep) :
    Unimodular (NormalForms.Matrix.Elementary.rightAccumulator log) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.rightAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.row op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.rightAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using ih hpair.2
      | col op =>
          have hpair :
              NormalForms.Matrix.Elementary.UnimodularStep (.col op : EMatrixStep R m n) ∧
                log.Forall NormalForms.Matrix.Elementary.UnimodularStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.rightAccumulator,
              NormalForms.Matrix.Elementary.UnimodularStep] using
            unimodular_mul (unimodular_columnOperationMatrix op hpair.1) (ih hpair.2)

/-- Predicate selecting row-only logs, used to collapse the right accumulator to `1`. -/
def IsRowStep {m n R : Type _} : EMatrixStep R m n -> Prop
  | .row _ => True
  | .col _ => False

/-- Predicate selecting column-only logs, used to collapse the left accumulator to `1`. -/
def IsColStep {m n R : Type _} : EMatrixStep R m n -> Prop
  | .row _ => False
  | .col _ => True

theorem rightAccumulator_eq_one_of_forall_isRow {m n R : Type _}
    [Fintype n] [DecidableEq n] [CommRing R]
    (log : EOperationLog R m n) (hlog : log.Forall IsRowStep) :
    NormalForms.Matrix.Elementary.rightAccumulator log = (1 : _root_.Matrix n n R) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.rightAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair : IsRowStep (.row op : EMatrixStep R m n) ∧ log.Forall IsRowStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.rightAccumulator, IsRowStep] using ih hpair.2
      | col op =>
          have hpair : IsRowStep (.col op : EMatrixStep R m n) ∧ log.Forall IsRowStep := by
            simpa [List.Forall]
              using hlog
          cases hpair.1

theorem leftAccumulator_eq_one_of_forall_isCol {m n R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    (log : EOperationLog R m n) (hlog : log.Forall IsColStep) :
    NormalForms.Matrix.Elementary.leftAccumulator log = (1 : _root_.Matrix m m R) := by
  induction log with
  | nil =>
      simp [NormalForms.Matrix.Elementary.leftAccumulator]
  | cons step log ih =>
      cases step with
      | row op =>
          have hpair : IsColStep (.row op : EMatrixStep R m n) ∧ log.Forall IsColStep := by
            simpa [List.Forall]
              using hlog
          cases hpair.1
      | col op =>
          have hpair : IsColStep (.col op : EMatrixStep R m n) ∧ log.Forall IsColStep := by
            simpa [List.Forall]
              using hlog
          simpa [NormalForms.Matrix.Elementary.leftAccumulator, IsColStep] using ih hpair.2

def TwoSidedCertificate.ofLog {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (log : EOperationLog R m n) :
    TwoSidedCertificate A :=
  { U := NormalForms.Matrix.Elementary.leftAccumulator log
    result := NormalForms.Matrix.Elementary.replayLog A log
    V := NormalForms.Matrix.Elementary.rightAccumulator log
    equation := NormalForms.Matrix.Elementary.replayLog_eq_left_right A log }

def LeftCertificate.ofRowLog {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (log : EOperationLog R m n)
    (hrow : log.Forall IsRowStep) :
    LeftCertificate A :=
  { U := NormalForms.Matrix.Elementary.leftAccumulator log
    result := NormalForms.Matrix.Elementary.replayLog A log
    equation := by
      simpa [rightAccumulator_eq_one_of_forall_isRow log hrow] using
        NormalForms.Matrix.Elementary.replayLog_eq_left_right A log }

end NormalForms.Matrix.Certificates



