/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Euclidean.ComputableOps
public import NormalForms.Matrix.Constructive

/-!
# Elementary Matrix Operations

This module provides executable row and column operations, operation
logs, small-step replay semantics, explicit elementary matrices, and
log-level left/right certificate accumulators.
-/

@[expose] public section

namespace NormalForms.Matrix.Elementary

inductive RowOperation (R : Type _) (m : Type _)
  | swap (i j : m)
  | add (src dst : m) (c : R)
  | smul (i : m) (c : R)

inductive ColumnOperation (R : Type _) (n : Type _)
  | swap (i j : n)
  | add (src dst : n) (c : R)
  | smul (i : n) (c : R)

inductive MatrixStep (R : Type _) (m n : Type _)
  | row (op : RowOperation R m)
  | col (op : ColumnOperation R n)

abbrev OperationLog (R : Type _) (m n : Type _) := List (MatrixStep R m n)

open scoped Matrix
open NormalForms.ComputableEuclideanOps

def applyRowOperation {m n R : Type _} [DecidableEq m] [Add R] [Mul R]
    (A : _root_.Matrix m n R) : RowOperation R m -> _root_.Matrix m n R
  | .swap i j => fun r c =>
      if r = i then
        A j c
      else if r = j then
        A i c
      else
        A r c
  | .add src dst k => fun r c =>
      if r = dst then
        A dst c + k * A src c
      else
        A r c
  | .smul i k => fun r c =>
      if r = i then
        k * A i c
      else
        A r c

def applyColumnOperation {m n R : Type _} [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) : ColumnOperation R n -> _root_.Matrix m n R
  | .swap i j => fun r c =>
      if c = i then
        A r j
      else if c = j then
        A r i
      else
        A r c
  | .add src dst k => fun r c =>
      if c = dst then
        A r dst + k * A r src
      else
        A r c
  | .smul i k => fun r c =>
      if c = i then
        k * A r i
      else
        A r c

def applyStep {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) : MatrixStep R m n -> _root_.Matrix m n R
  | .row op => applyRowOperation A op
  | .col op => applyColumnOperation A op

def replayLog {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) (log : OperationLog R m n) : _root_.Matrix m n R :=
  log.foldl applyStep A

@[simp] theorem replayLog_nil {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) :
    replayLog A ([] : OperationLog R m n) = A := by
  rfl

@[simp] theorem replayLog_cons {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) (step : MatrixStep R m n) (log : OperationLog R m n) :
    replayLog A (step :: log) = replayLog (applyStep A step) log := by
  rfl

theorem replayLog_append {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) (log₁ log₂ : OperationLog R m n) :
    replayLog A (log₁ ++ log₂) = replayLog (replayLog A log₁) log₂ := by
  induction log₁ generalizing A with
  | nil =>
      rfl
  | cons step rest ih =>
      simp [ih]

theorem basisRow_vecMul {m n R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (A : _root_.Matrix m n R) (i : m) :
    _root_.Matrix.vecMul ((1 : _root_.Matrix m m R) i) A = A i := by
  ext j
  simp only [_root_.Matrix.vecMul, dotProduct, _root_.Matrix.one_apply,
    ite_mul, one_mul, zero_mul]
  rw [NormalForms.Matrix.Constructive.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

theorem basisRow_smul_vecMul {m n R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (A : _root_.Matrix m n R) (i : m) (c : R) :
    _root_.Matrix.vecMul (c • (1 : _root_.Matrix m m R) i) A = c • A i := by
  rw [_root_.Matrix.smul_vecMul, basisRow_vecMul]

theorem basisRow_add_smul_vecMul {m n R : Type _} [Fintype m] [DecidableEq m]
    [CommRing R] (A : _root_.Matrix m n R) (src dst : m) (c : R) :
    _root_.Matrix.vecMul
        (((1 : _root_.Matrix m m R) dst) + c • (1 : _root_.Matrix m m R) src) A =
      A dst + c • A src := by
  rw [_root_.Matrix.add_vecMul, _root_.Matrix.smul_vecMul]
  rw [basisRow_vecMul, basisRow_vecMul]

theorem mulVec_basisCol {m n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (j : n) :
    _root_.Matrix.mulVec A (fun i => (1 : _root_.Matrix n n R) i j) = fun i => A i j := by
  ext i
  simp only [_root_.Matrix.mulVec, dotProduct, _root_.Matrix.one_apply,
    mul_ite, mul_one, mul_zero]
  rw [NormalForms.Matrix.Constructive.sum_ite_eq_right]
  simp only [Finset.mem_univ, if_true]

theorem mulVec_smul_basisCol {m n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (j : n) (c : R) :
    _root_.Matrix.mulVec A (c • fun i => (1 : _root_.Matrix n n R) i j) = fun i => c * A i j := by
  rw [_root_.Matrix.mulVec_smul, mulVec_basisCol]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]

theorem mulVec_add_smul_basisCol {m n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : n) (c : R) :
    _root_.Matrix.mulVec A
        ((fun i => (1 : _root_.Matrix n n R) i dst) +
          c • fun i => (1 : _root_.Matrix n n R) i src) =
      fun i => A i dst + c * A i src := by
  rw [_root_.Matrix.mulVec_add, _root_.Matrix.mulVec_smul, mulVec_basisCol, mulVec_basisCol]
  ext i
  simp [smul_eq_mul]

def rowScaleMatrix {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (i : m) (c : R) : _root_.Matrix m m R :=
  _root_.Matrix.updateRow (1 : _root_.Matrix m m R) i (c • (1 : _root_.Matrix m m R) i)

def columnScaleMatrix {n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (j : n) (c : R) : _root_.Matrix n n R :=
  _root_.Matrix.updateCol (1 : _root_.Matrix n n R) j (c • fun i => (1 : _root_.Matrix n n R) i j)

theorem rowScaleMatrix_mul {m n R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (A : _root_.Matrix m n R) (i : m) (c : R) :
    rowScaleMatrix i c * A = _root_.Matrix.updateRow A i (c • A i) := by
  unfold rowScaleMatrix
  rw [NormalForms.Matrix.Constructive.updateRow_mul,
    NormalForms.Matrix.Constructive.one_mul, basisRow_smul_vecMul]

theorem mul_columnScaleMatrix {m n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (j : n) (c : R) :
    A * columnScaleMatrix j c = _root_.Matrix.updateCol A j (fun i => c * A i j) := by
  unfold columnScaleMatrix
  rw [NormalForms.Matrix.Constructive.mul_updateCol,
    NormalForms.Matrix.Constructive.mul_one, mulVec_smul_basisCol]

theorem det_rowScaleMatrix {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (i : m) (c : R) :
    (rowScaleMatrix i c).det = c := by
  unfold rowScaleMatrix
  rw [_root_.Matrix.det_updateRow_smul, _root_.Matrix.updateRow_eq_self, _root_.Matrix.det_one]
  simp

theorem det_columnScaleMatrix {n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (j : n) (c : R) :
    (columnScaleMatrix j c).det = c := by
  unfold columnScaleMatrix
  rw [_root_.Matrix.det_updateCol_smul, _root_.Matrix.updateCol_eq_self, _root_.Matrix.det_one]
  simp

def rowOperationMatrix {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R] :
    RowOperation R m -> _root_.Matrix m m R
  | .swap i j =>
      applyRowOperation (1 : _root_.Matrix m m R) (.swap i j)
  | .add src dst c =>
      _root_.Matrix.updateRow (1 : _root_.Matrix m m R) dst
        ((1 : _root_.Matrix m m R) dst + c • (1 : _root_.Matrix m m R) src)
  | .smul i c => rowScaleMatrix i c

def columnOperationMatrix {n R : Type _} [Fintype n] [DecidableEq n] [CommRing R] :
    ColumnOperation R n -> _root_.Matrix n n R
  | .swap i j =>
      applyColumnOperation (1 : _root_.Matrix n n R) (.swap i j)
  | .add src dst c =>
      _root_.Matrix.updateCol (1 : _root_.Matrix n n R) dst
        ((fun i => (1 : _root_.Matrix n n R) i dst) + c • fun i => (1 : _root_.Matrix n n R) i src)
  | .smul i c => columnScaleMatrix i c

theorem rowOperationMatrix_mul {m n R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (A : _root_.Matrix m n R) (op : RowOperation R m) :
    rowOperationMatrix op * A = applyRowOperation A op := by
  cases op with
  | swap i j =>
      ext r col
      change
        _root_.Matrix.vecMul
            (applyRowOperation (1 : _root_.Matrix m m R) (.swap i j) r) A col =
          applyRowOperation A (.swap i j) r col
      by_cases hr₁ : r = i
      · subst hr₁
        simp only [applyRowOperation, if_pos]
        exact congrFun (basisRow_vecMul A j) col
      · by_cases hr₂ : r = j
        · subst hr₂
          simp only [applyRowOperation, hr₁, if_false, if_pos]
          exact congrFun (basisRow_vecMul A i) col
        · simp only [applyRowOperation, hr₁, hr₂, if_false]
          exact congrFun (basisRow_vecMul A r) col
  | add src dst c =>
      unfold rowOperationMatrix
      rw [NormalForms.Matrix.Constructive.updateRow_mul,
        NormalForms.Matrix.Constructive.one_mul, basisRow_add_smul_vecMul]
      ext r col
      by_cases hr : r = dst
      · subst hr
        simp [applyRowOperation, _root_.Matrix.updateRow_apply, smul_eq_mul]
      · simp [applyRowOperation, _root_.Matrix.updateRow_apply, hr]
  | smul i c =>
      rw [rowOperationMatrix, rowScaleMatrix_mul]
      ext r col
      by_cases hr : r = i
      · subst hr
        simp [applyRowOperation, _root_.Matrix.updateRow_apply, smul_eq_mul]
      · simp [applyRowOperation, _root_.Matrix.updateRow_apply, hr]

theorem mul_columnOperationMatrix {m n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (op : ColumnOperation R n) :
    A * columnOperationMatrix op = applyColumnOperation A op := by
  cases op with
  | swap i j =>
      ext r col
      change
        _root_.Matrix.mulVec A
            (fun x => applyColumnOperation (1 : _root_.Matrix n n R) (.swap i j) x col) r =
          applyColumnOperation A (.swap i j) r col
      by_cases hc₁ : col = i
      · subst hc₁
        simp only [applyColumnOperation, if_pos]
        exact congrFun (mulVec_basisCol A j) r
      · by_cases hc₂ : col = j
        · subst hc₂
          simp only [applyColumnOperation, hc₁, if_false, if_pos]
          exact congrFun (mulVec_basisCol A i) r
        · simp only [applyColumnOperation, hc₁, hc₂, if_false]
          exact congrFun (mulVec_basisCol A col) r
  | add src dst c =>
      unfold columnOperationMatrix
      rw [NormalForms.Matrix.Constructive.mul_updateCol,
        NormalForms.Matrix.Constructive.mul_one, mulVec_add_smul_basisCol]
      ext r col
      by_cases hc : col = dst
      · subst hc
        simp [applyColumnOperation]
      · simp [applyColumnOperation, hc]
  | smul i c =>
      rw [columnOperationMatrix, mul_columnScaleMatrix]
      ext r col
      by_cases hc : col = i
      · subst hc
        simp [applyColumnOperation]
      · simp [applyColumnOperation, hc]

theorem det_rowAddMatrix_of_ne {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (src dst : m) (c : R) (h : src ≠ dst) :
    (rowOperationMatrix (.add src dst c : RowOperation R m)).det = 1 := by
  unfold rowOperationMatrix
  rw [
    _root_.Matrix.det_updateRow_add_smul_self
      (A := (1 : _root_.Matrix m m R)) (i := dst) (j := src) h.symm c,
    _root_.Matrix.det_one
  ]

theorem det_columnAddMatrix_of_ne {n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (src dst : n) (c : R) (h : src ≠ dst) :
    (columnOperationMatrix (.add src dst c : ColumnOperation R n)).det = 1 := by
  unfold columnOperationMatrix
  change
    (_root_.Matrix.updateCol (1 : _root_.Matrix n n R) dst
      (fun k => (1 : _root_.Matrix n n R) k dst + c * (1 : _root_.Matrix n n R) k src)).det =
        1
  simpa only [_root_.Matrix.det_one, smul_eq_mul] using
    (_root_.Matrix.det_updateCol_add_smul_self
      (A := (1 : _root_.Matrix n n R)) (i := dst) (j := src) h.symm c)

def UnimodularRowOperation {m R : Type _} [CommRing R] : RowOperation R m -> Prop
  | .swap _ _ => True
  | .add src dst _ => src ≠ dst
  | .smul _ c => IsUnit c

def UnimodularColumnOperation {n R : Type _} [CommRing R] : ColumnOperation R n -> Prop
  | .swap _ _ => True
  | .add src dst _ => src ≠ dst
  | .smul _ c => IsUnit c

def UnimodularStep {m n R : Type _} [CommRing R] : MatrixStep R m n -> Prop
  | .row op => UnimodularRowOperation op
  | .col op => UnimodularColumnOperation op

def leftAccumulator {m n R : Type _} [Fintype m] [DecidableEq m] [CommRing R] :
    OperationLog R m n -> _root_.Matrix m m R
  | [] => 1
  | .row op :: log => leftAccumulator log * rowOperationMatrix op
  | .col _ :: log => leftAccumulator log

def rightAccumulator {m n R : Type _} [Fintype n] [DecidableEq n] [CommRing R] :
    OperationLog R m n -> _root_.Matrix n n R
  | [] => 1
  | .row _ :: log => rightAccumulator log
  | .col op :: log => columnOperationMatrix op * rightAccumulator log

@[simp] theorem leftAccumulator_nil {m n R : Type _} [Fintype m] [DecidableEq m] [CommRing R] :
    leftAccumulator ([] : OperationLog R m n) = (1 : _root_.Matrix m m R) := by
  rfl

@[simp] theorem rightAccumulator_nil {m n R : Type _} [Fintype n] [DecidableEq n] [CommRing R] :
    rightAccumulator ([] : OperationLog R m n) = (1 : _root_.Matrix n n R) := by
  rfl

theorem replayLog_eq_left_right {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [CommRing R] (A : _root_.Matrix m n R) (log : OperationLog R m n) :
    leftAccumulator log * A * rightAccumulator log = replayLog A log := by
  induction log generalizing A with
  | nil =>
      simp [leftAccumulator, rightAccumulator, replayLog]
  | cons step rest ih =>
      cases step with
      | row op =>
          calc
            leftAccumulator (.row op :: rest) * A * rightAccumulator (.row op :: rest)
                = leftAccumulator rest * (rowOperationMatrix op * A) * rightAccumulator rest := by
                    simp [leftAccumulator, rightAccumulator, Matrix.mul_assoc]
            _ = replayLog (rowOperationMatrix op * A) rest := ih _
            _ = replayLog (applyStep A (.row op)) rest := by
                  simp [applyStep, rowOperationMatrix_mul]
            _ = replayLog A (.row op :: rest) := by simp [replayLog_cons]
      | col op =>
          calc
            leftAccumulator (.col op :: rest) * A * rightAccumulator (.col op :: rest)
                = leftAccumulator rest *
                    (A * columnOperationMatrix op) * rightAccumulator rest := by
                    simp [leftAccumulator, rightAccumulator, Matrix.mul_assoc]
            _ = replayLog (A * columnOperationMatrix op) rest := ih _
            _ = replayLog (applyStep A (.col op)) rest := by
                  simp [applyStep, mul_columnOperationMatrix]
            _ = replayLog A (.col op :: rest) := by simp [replayLog_cons]

def bezoutCoreMatrix {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) : _root_.Matrix (Fin 2) (Fin 2) R :=
  let data := ComputableEuclideanOps.xgcd a b
  !![data.leftCoeff, data.rightCoeff;
     -(quot b data.gcd), quot a data.gcd]

def bezoutReductionMatrix {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) : _root_.Matrix (Fin 2) (Fin 2) R :=
  let g := (ComputableEuclideanOps.xgcd a b).gcd
  if isZeroB g = true then 1 else bezoutCoreMatrix a b

theorem bezoutReductionMatrix_mulVec {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    _root_.Matrix.mulVec (bezoutReductionMatrix a b) ![a, b] =
      ![(ComputableEuclideanOps.xgcd a b).gcd, 0] := by
  by_cases hg : (ComputableEuclideanOps.xgcd a b).gcd = 0
  · rcases (xgcd_gcd_eq_zero_iff a b).mp hg with ⟨ha, hb⟩
    have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd = true :=
      (isZeroB_eq_true_iff _).2 hg
    rw [bezoutReductionMatrix, if_pos hgb]
    rw [NormalForms.Matrix.Constructive.one_mulVec]
    ext i
    fin_cases i
    · simpa using ha.trans hg.symm
    · simpa using hb
  · have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd ≠ true :=
      fun h => hg ((isZeroB_eq_true_iff _).1 h)
    rw [bezoutReductionMatrix, if_neg hgb]
    ext i
    fin_cases i
    · rw [_root_.Matrix.mulVec, dotProduct,
        NormalForms.Matrix.Constructive.sum_univ_two]
      simpa [bezoutCoreMatrix, mul_comm] using (xgcd_bezout a b)
    · suffices h :
          -(quot b (ComputableEuclideanOps.xgcd a b).gcd) * a +
              quot a (ComputableEuclideanOps.xgcd a b).gcd * b = 0 by
        rw [_root_.Matrix.mulVec, dotProduct,
          NormalForms.Matrix.Constructive.sum_univ_two]
        simpa [bezoutCoreMatrix] using h
      apply mul_left_cancel_of_ne_zero hg
      rw [mul_zero]
      calc
        (ComputableEuclideanOps.xgcd a b).gcd *
            (-(quot b (ComputableEuclideanOps.xgcd a b).gcd) * a +
              quot a (ComputableEuclideanOps.xgcd a b).gcd * b) =
          -((ComputableEuclideanOps.xgcd a b).gcd *
              (quot b (ComputableEuclideanOps.xgcd a b).gcd * a)) +
            (ComputableEuclideanOps.xgcd a b).gcd *
              (quot a (ComputableEuclideanOps.xgcd a b).gcd * b) := by
                ring
        _ = -(((ComputableEuclideanOps.xgcd a b).gcd *
                quot b (ComputableEuclideanOps.xgcd a b).gcd) * a) +
              ((ComputableEuclideanOps.xgcd a b).gcd *
                quot a (ComputableEuclideanOps.xgcd a b).gcd) * b := by
                ring
        _ = -(b * a) + a * b := by
              rw [mul_quot_cancel_of_dvd hg (xgcd_gcd_dvd_right a b),
                mul_quot_cancel_of_dvd hg (xgcd_gcd_dvd_left a b)]
        _ = 0 := by ring

theorem vecMul_bezoutReductionMatrix_transpose {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    _root_.Matrix.vecMul ![a, b] (bezoutReductionMatrix a b).transpose =
      ![(ComputableEuclideanOps.xgcd a b).gcd, 0] := by
  simpa using
    ((_root_.Matrix.vecMul_transpose (bezoutReductionMatrix a b) ![a, b]).trans
      (bezoutReductionMatrix_mulVec a b))

/-- The Bézout coefficients after dividing both inputs by the computed gcd. -/
theorem bezoutDivIdentity {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (hg : (ComputableEuclideanOps.xgcd a b).gcd ≠ 0) :
    (ComputableEuclideanOps.xgcd a b).leftCoeff *
        quot a (ComputableEuclideanOps.xgcd a b).gcd +
      (ComputableEuclideanOps.xgcd a b).rightCoeff *
        quot b (ComputableEuclideanOps.xgcd a b).gcd = 1 := by
  apply mul_left_cancel_of_ne_zero hg
  rw [mul_one]
  calc
    (ComputableEuclideanOps.xgcd a b).gcd *
        ((ComputableEuclideanOps.xgcd a b).leftCoeff *
            quot a (ComputableEuclideanOps.xgcd a b).gcd +
          (ComputableEuclideanOps.xgcd a b).rightCoeff *
            quot b (ComputableEuclideanOps.xgcd a b).gcd) =
      (ComputableEuclideanOps.xgcd a b).leftCoeff *
          ((ComputableEuclideanOps.xgcd a b).gcd *
            quot a (ComputableEuclideanOps.xgcd a b).gcd) +
        (ComputableEuclideanOps.xgcd a b).rightCoeff *
          ((ComputableEuclideanOps.xgcd a b).gcd *
            quot b (ComputableEuclideanOps.xgcd a b).gcd) := by
              ring
    _ = (ComputableEuclideanOps.xgcd a b).leftCoeff * a +
          (ComputableEuclideanOps.xgcd a b).rightCoeff * b := by
          rw [mul_quot_cancel_of_dvd hg (xgcd_gcd_dvd_left a b),
            mul_quot_cancel_of_dvd hg (xgcd_gcd_dvd_right a b)]
    _ = (ComputableEuclideanOps.xgcd a b).gcd := by
          simpa [mul_comm] using xgcd_bezout a b

theorem det_bezoutReductionMatrix {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    (bezoutReductionMatrix a b).det = 1 := by
  by_cases hg : (ComputableEuclideanOps.xgcd a b).gcd = 0
  · have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd = true :=
      (isZeroB_eq_true_iff _).2 hg
    simp [bezoutReductionMatrix, hgb]
  · have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd ≠ true :=
      fun h => hg ((isZeroB_eq_true_iff _).1 h)
    have hdet := bezoutDivIdentity a b hg
    simpa [bezoutReductionMatrix, hgb, bezoutCoreMatrix, _root_.Matrix.det_fin_two_of,
      sub_eq_add_neg] using hdet

/-- Explicit inverse of the 2x2 Bézout reduction primitive. -/
def bezoutReductionInverseMatrix {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) : _root_.Matrix (Fin 2) (Fin 2) R :=
  let data := ComputableEuclideanOps.xgcd a b
  if isZeroB data.gcd = true then
    1
  else
    !![quot a data.gcd, -data.rightCoeff;
       quot b data.gcd, data.leftCoeff]

theorem bezoutReductionInverseMatrix_mul {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    bezoutReductionInverseMatrix a b * bezoutReductionMatrix a b = 1 := by
  by_cases hg : (ComputableEuclideanOps.xgcd a b).gcd = 0
  · have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd = true :=
      (isZeroB_eq_true_iff _).2 hg
    rw [bezoutReductionInverseMatrix, bezoutReductionMatrix, if_pos hgb, if_pos hgb]
    exact NormalForms.Matrix.Constructive.one_mul 1
  · have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd ≠ true :=
      fun h => hg ((isZeroB_eq_true_iff _).1 h)
    have hid := bezoutDivIdentity a b hg
    simp only [quot_eq] at hid
    rw [bezoutReductionInverseMatrix, bezoutReductionMatrix, if_neg hgb, if_neg hgb]
    ext i j
    fin_cases i <;> fin_cases j <;>
      rw [_root_.Matrix.mul_apply,
        NormalForms.Matrix.Constructive.sum_univ_two] <;>
      simp [bezoutCoreMatrix] <;>
      ring_nf at hid ⊢ <;>
      assumption

theorem bezoutReductionMatrix_mul_inverse {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    bezoutReductionMatrix a b * bezoutReductionInverseMatrix a b = 1 := by
  by_cases hg : (ComputableEuclideanOps.xgcd a b).gcd = 0
  · have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd = true :=
      (isZeroB_eq_true_iff _).2 hg
    rw [bezoutReductionMatrix, bezoutReductionInverseMatrix, if_pos hgb, if_pos hgb]
    exact NormalForms.Matrix.Constructive.one_mul 1
  · have hgb : isZeroB (ComputableEuclideanOps.xgcd a b).gcd ≠ true :=
      fun h => hg ((isZeroB_eq_true_iff _).1 h)
    have hid := bezoutDivIdentity a b hg
    simp only [quot_eq] at hid
    rw [bezoutReductionMatrix, bezoutReductionInverseMatrix, if_neg hgb, if_neg hgb]
    ext i j
    fin_cases i <;> fin_cases j <;>
      rw [_root_.Matrix.mul_apply,
        NormalForms.Matrix.Constructive.sum_univ_two] <;>
      simp [bezoutCoreMatrix] <;>
      ring_nf at hid ⊢ <;>
      assumption
end NormalForms.Matrix.Elementary
