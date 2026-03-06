import NormalForms.Basic

/-!
# Elementary Matrix Operations

This module provides executable row and column operations, operation
logs, small-step replay semantics, explicit elementary matrices, and
log-level left/right certificate accumulators.
-/

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

theorem basisRow_vecMul {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [CommRing R] (A : _root_.Matrix m n R) (i : m) :
    _root_.Matrix.vecMul ((1 : _root_.Matrix m m R) i) A = A i := by
  ext j
  rw [_root_.Matrix.vecMul, dotProduct, Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    have hix : i ≠ x := by simpa [eq_comm] using hx
    simp [_root_.Matrix.one_apply, hix]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem basisRow_smul_vecMul {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [CommRing R] (A : _root_.Matrix m n R) (i : m) (c : R) :
    _root_.Matrix.vecMul (c • (1 : _root_.Matrix m m R) i) A = c • A i := by
  ext j
  rw [_root_.Matrix.vecMul, dotProduct, Finset.sum_eq_single i]
  · simp [Pi.smul_apply, smul_eq_mul]
  · intro x _ hx
    have hix : i ≠ x := by simpa [eq_comm] using hx
    simp [Pi.smul_apply, smul_eq_mul, _root_.Matrix.one_apply, hix]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem basisRow_add_smul_vecMul {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [CommRing R] (A : _root_.Matrix m n R) (src dst : m) (c : R) :
    _root_.Matrix.vecMul (((1 : _root_.Matrix m m R) dst) + c • (1 : _root_.Matrix m m R) src) A =
      A dst + c • A src := by
  rw [_root_.Matrix.add_vecMul, _root_.Matrix.smul_vecMul]
  rw [basisRow_vecMul, basisRow_vecMul]

theorem mulVec_basisCol {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [CommRing R] (A : _root_.Matrix m n R) (j : n) :
    _root_.Matrix.mulVec A (fun i => (1 : _root_.Matrix n n R) i j) = fun i => A i j := by
  ext i
  rw [_root_.Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp
  · intro x _ hx
    simp [_root_.Matrix.one_apply, hx]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem mulVec_smul_basisCol {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [CommRing R] (A : _root_.Matrix m n R) (j : n) (c : R) :
    _root_.Matrix.mulVec A (c • fun i => (1 : _root_.Matrix n n R) i j) = fun i => c * A i j := by
  ext i
  rw [_root_.Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  · intro x _ hx
    simp [Pi.smul_apply, smul_eq_mul, _root_.Matrix.one_apply, hx]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem mulVec_add_smul_basisCol {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [CommRing R] (A : _root_.Matrix m n R) (src dst : n) (c : R) :
    _root_.Matrix.mulVec A ((fun i => (1 : _root_.Matrix n n R) i dst) + c • fun i => (1 : _root_.Matrix n n R) i src) =
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

theorem rowScaleMatrix_mul {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [CommRing R] (A : _root_.Matrix m n R) (i : m) (c : R) :
    rowScaleMatrix i c * A = _root_.Matrix.updateRow A i (c • A i) := by
  unfold rowScaleMatrix
  rw [_root_.Matrix.updateRow_mul, _root_.Matrix.one_mul, basisRow_smul_vecMul]

theorem mul_columnScaleMatrix {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [CommRing R] (A : _root_.Matrix m n R) (j : n) (c : R) :
    A * columnScaleMatrix j c = _root_.Matrix.updateCol A j (fun i => c * A i j) := by
  unfold columnScaleMatrix
  rw [_root_.Matrix.mul_updateCol, _root_.Matrix.mul_one, mulVec_smul_basisCol]

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
  | .swap i j => _root_.Matrix.swap R i j
  | .add src dst c =>
      _root_.Matrix.updateRow (1 : _root_.Matrix m m R) dst
        ((1 : _root_.Matrix m m R) dst + c • (1 : _root_.Matrix m m R) src)
  | .smul i c => rowScaleMatrix i c

def columnOperationMatrix {n R : Type _} [Fintype n] [DecidableEq n] [CommRing R] :
    ColumnOperation R n -> _root_.Matrix n n R
  | .swap i j => _root_.Matrix.swap R i j
  | .add src dst c =>
      _root_.Matrix.updateCol (1 : _root_.Matrix n n R) dst
        ((fun i => (1 : _root_.Matrix n n R) i dst) + c • fun i => (1 : _root_.Matrix n n R) i src)
  | .smul i c => columnScaleMatrix i c

theorem rowOperationMatrix_mul {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [CommRing R] (A : _root_.Matrix m n R) (op : RowOperation R m) :
    rowOperationMatrix op * A = applyRowOperation A op := by
  cases op with
  | swap i j =>
      ext r col
      by_cases hr₁ : r = i
      · subst hr₁
        simpa [rowOperationMatrix, applyRowOperation] using
          (_root_.Matrix.swap_mul_apply_left (R := R) (i := i) (j := j) (a := col) (g := A))
      · by_cases hr₂ : r = j
        · subst hr₂
          simpa [rowOperationMatrix, applyRowOperation, hr₁] using
            (_root_.Matrix.swap_mul_apply_right (R := R) (i := i) (j := j) (a := col) (g := A))
        · simpa [rowOperationMatrix, applyRowOperation, hr₁, hr₂] using
            (_root_.Matrix.swap_mul_of_ne (R := R) (i := i) (j := j) (a := r) (b := col) hr₁ hr₂ A)
  | add src dst c =>
      unfold rowOperationMatrix
      rw [_root_.Matrix.updateRow_mul, _root_.Matrix.one_mul, basisRow_add_smul_vecMul]
      ext r col
      by_cases hr : r = dst
      · subst hr
        simp [applyRowOperation, _root_.Matrix.updateRow_apply, smul_eq_mul]
      · simp [applyRowOperation, _root_.Matrix.updateRow_apply, hr]
  | smul i c =>
      simp [rowOperationMatrix, rowScaleMatrix_mul]
      ext r col
      by_cases hr : r = i
      · subst hr
        simp [applyRowOperation, _root_.Matrix.updateRow_apply, smul_eq_mul]
      · simp [applyRowOperation, _root_.Matrix.updateRow_apply, hr]

theorem mul_columnOperationMatrix {m n R : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [CommRing R] (A : _root_.Matrix m n R) (op : ColumnOperation R n) :
    A * columnOperationMatrix op = applyColumnOperation A op := by
  cases op with
  | swap i j =>
      ext r col
      by_cases hc₁ : col = i
      · subst hc₁
        simpa [columnOperationMatrix, applyColumnOperation] using
          (_root_.Matrix.mul_swap_apply_left (R := R) (i := i) (j := j) (a := r) (g := A))
      · by_cases hc₂ : col = j
        · subst hc₂
          simpa [columnOperationMatrix, applyColumnOperation, hc₁] using
            (_root_.Matrix.mul_swap_apply_right (R := R) (i := i) (j := j) (a := r) (g := A))
        · simpa [columnOperationMatrix, applyColumnOperation, hc₁, hc₂] using
            (_root_.Matrix.mul_swap_of_ne (R := R) (i := i) (j := j) (a := r) (b := col) hc₁ hc₂ A)
  | add src dst c =>
      unfold columnOperationMatrix
      rw [_root_.Matrix.mul_updateCol, _root_.Matrix.mul_one, mulVec_add_smul_basisCol]
      ext r col
      by_cases hc : col = dst
      · subst hc
        simp [applyColumnOperation, _root_.Matrix.updateCol_apply]
      · simp [applyColumnOperation, _root_.Matrix.updateCol_apply, hc]
  | smul i c =>
      simp [columnOperationMatrix, mul_columnScaleMatrix]
      ext r col
      by_cases hc : col = i
      · subst hc
        simp [applyColumnOperation, _root_.Matrix.updateCol_apply]
      · simp [applyColumnOperation, _root_.Matrix.updateCol_apply, hc]

theorem det_rowAddMatrix_of_ne {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (src dst : m) (c : R) (h : src ≠ dst) :
    (rowOperationMatrix (.add src dst c : RowOperation R m)).det = 1 := by
  unfold rowOperationMatrix
  rw [_root_.Matrix.det_updateRow_add_smul_self (A := (1 : _root_.Matrix m m R)) (i := dst) (j := src)
    h.symm c, _root_.Matrix.det_one]

theorem det_columnAddMatrix_of_ne {n R : Type _} [Fintype n] [DecidableEq n] [CommRing R]
    (src dst : n) (c : R) (h : src ≠ dst) :
    (columnOperationMatrix (.add src dst c : ColumnOperation R n)).det = 1 := by
  simpa [columnOperationMatrix, _root_.Matrix.det_one] using
    (_root_.Matrix.det_updateCol_add_smul_self (A := (1 : _root_.Matrix n n R)) (i := dst) (j := src)
      h.symm c)

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
            _ = replayLog (applyStep A (.row op)) rest := by simp [applyStep, rowOperationMatrix_mul]
            _ = replayLog A (.row op :: rest) := by simp [replayLog_cons]
      | col op =>
          calc
            leftAccumulator (.col op :: rest) * A * rightAccumulator (.col op :: rest)
                = leftAccumulator rest * (A * columnOperationMatrix op) * rightAccumulator rest := by
                    simp [leftAccumulator, rightAccumulator, Matrix.mul_assoc]
            _ = replayLog (A * columnOperationMatrix op) rest := ih _
            _ = replayLog (applyStep A (.col op)) rest := by simp [applyStep, mul_columnOperationMatrix]
            _ = replayLog A (.col op :: rest) := by simp [replayLog_cons]

def bezoutCoreMatrix {R : Type _} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    _root_.Matrix (Fin 2) (Fin 2) R :=
  !![EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b;
     -(b / EuclideanDomain.gcd a b), a / EuclideanDomain.gcd a b]

def bezoutReductionMatrix {R : Type _} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    _root_.Matrix (Fin 2) (Fin 2) R :=
  if EuclideanDomain.gcd a b = 0 then 1 else bezoutCoreMatrix a b

theorem bezoutReductionMatrix_mulVec {R : Type _} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    _root_.Matrix.mulVec (bezoutReductionMatrix a b) ![a, b] = ![EuclideanDomain.gcd a b, 0] := by
  by_cases hg : EuclideanDomain.gcd a b = 0
  · rcases EuclideanDomain.gcd_eq_zero_iff.mp hg with ⟨ha, hb⟩
    rw [bezoutReductionMatrix, if_pos hg]
    ext i <;> fin_cases i <;> simp [ha, hb]
  · rw [bezoutReductionMatrix, if_neg hg]
    ext i <;> fin_cases i
    · simp [bezoutCoreMatrix, _root_.Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        EuclideanDomain.gcd_eq_gcd_ab, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]
    · simp [bezoutCoreMatrix, _root_.Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      apply (mul_left_cancel₀ hg)
      rw [mul_zero, mul_add, mul_neg]
      calc
        -(EuclideanDomain.gcd a b * (b / EuclideanDomain.gcd a b * a)) +
            EuclideanDomain.gcd a b * (a / EuclideanDomain.gcd a b * b)
            = -((EuclideanDomain.gcd a b * (b / EuclideanDomain.gcd a b)) * a) +
                (EuclideanDomain.gcd a b * (a / EuclideanDomain.gcd a b)) * b := by ring
        _ = -(b * a) + a * b := by
              rw [EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_right a b),
                EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_left a b)]
        _ = 0 := by ring

theorem vecMul_bezoutReductionMatrix_transpose {R : Type _} [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    _root_.Matrix.vecMul ![a, b] (bezoutReductionMatrix a b).transpose = ![EuclideanDomain.gcd a b, 0] := by
  simpa using
    ((_root_.Matrix.vecMul_transpose (bezoutReductionMatrix a b) ![a, b]).trans
      (bezoutReductionMatrix_mulVec a b))

theorem det_bezoutReductionMatrix {R : Type _} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    (bezoutReductionMatrix a b).det = 1 := by
  by_cases hg : EuclideanDomain.gcd a b = 0
  · simp [bezoutReductionMatrix, hg]
  · simp [bezoutReductionMatrix, hg, bezoutCoreMatrix, _root_.Matrix.det_fin_two_of]
    apply (mul_left_cancel₀ hg)
    rw [mul_one]
    calc
      EuclideanDomain.gcd a b *
          (EuclideanDomain.gcdA a b * (a / EuclideanDomain.gcd a b) +
            EuclideanDomain.gcdB a b * (b / EuclideanDomain.gcd a b))
          = EuclideanDomain.gcdA a b *
              (EuclideanDomain.gcd a b * (a / EuclideanDomain.gcd a b)) +
              EuclideanDomain.gcdB a b *
                (EuclideanDomain.gcd a b * (b / EuclideanDomain.gcd a b)) := by ring
      _ = EuclideanDomain.gcdA a b * a + EuclideanDomain.gcdB a b * b := by
            rw [EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_left a b),
              EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_right a b)]
      _ = EuclideanDomain.gcd a b := by
            simpa [EuclideanDomain.gcd_eq_gcd_ab, add_assoc, add_left_comm, add_comm,
              mul_assoc, mul_left_comm, mul_comm]

end NormalForms.Matrix.Elementary






