import NormalForms.Matrix.Certificates

/-!
# Hermite Normal Form API

Executable row-style Hermite normal forms over Euclidean domains.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates

/-- A Euclidean domain whose remainder choice is canonical, so `%` is idempotent. -/
class CanonicalMod (R : Type _) [EuclideanDomain R] : Prop where
  mod_mod : ∀ a b : R, (a % b) % b = a % b

instance : CanonicalMod Int where
  mod_mod := Int.emod_emod


def firstNonzero? {R : Type _} [Zero R] [DecidableEq R] :
    {n : Nat} -> (Fin n -> R) -> Option (Fin n)
  | 0, _ => none
  | _ + 1, row =>
      if row 0 = 0 then
        Option.map Fin.succ (firstNonzero? fun j => row j.succ)
      else
        some 0


def tailCols {m n : Nat} {R : Type _} (A : _root_.Matrix (Fin m) (Fin (n + 1)) R) :
    _root_.Matrix (Fin m) (Fin n) R :=
  fun i j => A i j.succ


def lowerRight {m n : Nat} {R : Type _} (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) :
    _root_.Matrix (Fin m) (Fin n) R :=
  fun i j => A i.succ j.succ


inductive IsHermiteNormalFormFin {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
    {m n : Nat} -> _root_.Matrix (Fin m) (Fin n) R -> Prop
  | emptyRows {n : Nat} (A : _root_.Matrix (Fin 0) (Fin n) R) :
      IsHermiteNormalFormFin A
  | emptyCols {m : Nat} (A : _root_.Matrix (Fin m) (Fin 0) R) :
      IsHermiteNormalFormFin A
  | zeroCol {m n : Nat} (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
      (hzero : ∀ i, A i 0 = 0)
      (hTail : IsHermiteNormalFormFin (tailCols A)) :
      IsHermiteNormalFormFin A
  | pivot {m n : Nat} (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
      (hpivot : A 0 0 ≠ 0)
      (hnorm : A 0 0 = normalize (A 0 0))
      (hbelow : ∀ i : Fin m, A i.succ 0 = 0)
      (hLower : IsHermiteNormalFormFin (lowerRight A))
      (hreduced : ∀ i : Fin m,
        match firstNonzero? (fun j : Fin n => A i.succ j.succ) with
        | none => True
        | some j => A 0 j.succ = A 0 j.succ % A i.succ j.succ) :
      IsHermiteNormalFormFin A


def IsHermiteNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : Prop :=
  IsHermiteNormalFormFin
    (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)


structure RowTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix m n R) where
  B : _root_.Matrix m n R
  log : OperationLog R m n
  rowLog : log.Forall IsRowStep
  unimodular : log.Forall UnimodularStep
  replay_eq : replayLog A log = B


theorem listForall_append_iff {α : Type _} {p : α -> Prop} (xs ys : List α) :
    (xs ++ ys).Forall p ↔ xs.Forall p ∧ ys.Forall p := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, and_assoc]


def RowTransform.refl {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix m n R) : RowTransform A :=
  { B := A
    log := []
    rowLog := by simp
    unimodular := by simp
    replay_eq := by simp }


def RowTransform.singleton {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix m n R) (op : RowOperation R m) (hop : UnimodularRowOperation op) :
    RowTransform A :=
  { B := applyRowOperation A op
    log := [.row op]
    rowLog := by simp [IsRowStep]
    unimodular := by
      simpa [List.Forall, UnimodularStep] using hop
    replay_eq := by rfl }


def RowTransform.trans {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] [NormalizationMonoid R]
    {A : _root_.Matrix m n R} (first : RowTransform A) (second : RowTransform first.B) :
    RowTransform A :=
  { B := second.B
    log := first.log ++ second.log
    rowLog := (listForall_append_iff first.log second.log).2 ⟨first.rowLog, second.rowLog⟩
    unimodular := (listForall_append_iff first.log second.log).2
      ⟨first.unimodular, second.unimodular⟩
    replay_eq := by
      rw [replayLog_append, first.replay_eq, second.replay_eq] }


structure LeftTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  B : _root_.Matrix m n R
  left_mul : U * A = B
  unimodular : Unimodular U


def LeftTransform.refl {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) : LeftTransform A :=
  { U := 1
    B := A
    left_mul := by simp
    unimodular := unimodular_one }


def LeftTransform.trans {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (first : LeftTransform A) (second : LeftTransform first.B) :
    LeftTransform A :=
  { U := second.U * first.U
    B := second.B
    left_mul := by
      calc
        (second.U * first.U) * A = second.U * (first.U * A) := by
          rw [Matrix.mul_assoc]
        _ = second.U * first.B := by rw [first.left_mul]
        _ = second.B := second.left_mul
    unimodular := unimodular_mul second.unimodular first.unimodular }


def LeftTransform.ofRowTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] [NormalizationMonoid R]
    {A : _root_.Matrix m n R} (t : RowTransform A) : LeftTransform A :=
  { U := leftAccumulator t.log
    B := t.B
    left_mul := by
      have hright := rightAccumulator_eq_one_of_forall_isRow t.log t.rowLog
      have hmul := replayLog_eq_left_right A t.log
      simpa [hright, t.replay_eq] using hmul
    unimodular := leftAccumulator_unimodular_of_forall t.log t.unimodular }


def LeftTransform.swap {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i j : m) : LeftTransform A :=
  { U := rowOperationMatrix (.swap i j)
    B := applyRowOperation A (.swap i j)
    left_mul := rowOperationMatrix_mul A (.swap i j)
    unimodular := unimodular_rowOperationMatrix (.swap i j) (by trivial) }


def LeftTransform.add {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : m) (c : R) (hne : src ≠ dst) :
    LeftTransform A :=
  { U := rowOperationMatrix (.add src dst c)
    B := applyRowOperation A (.add src dst c)
    left_mul := rowOperationMatrix_mul A (.add src dst c)
    unimodular := unimodular_rowOperationMatrix (.add src dst c) hne }


def LeftTransform.unitSmul {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i : m) (c : R) (hc : IsUnit c) : LeftTransform A :=
  { U := rowOperationMatrix (.smul i c)
    B := applyRowOperation A (.smul i c)
    left_mul := rowOperationMatrix_mul A (.smul i c)
    unimodular := unimodular_rowOperationMatrix (.smul i c) hc }


def mapRowOperation {m m' R : Type _} (f : m -> m') : RowOperation R m -> RowOperation R m'
  | .swap i j => .swap (f i) (f j)
  | .add src dst c => .add (f src) (f dst) c
  | .smul i c => .smul (f i) c


def mapColumnOperation {n n' R : Type _} (f : n -> n') :
    ColumnOperation R n -> ColumnOperation R n'
  | .swap i j => .swap (f i) (f j)
  | .add src dst c => .add (f src) (f dst) c
  | .smul i c => .smul (f i) c


def mapStep {m m' n n' R : Type _} (fm : m -> m') (fn : n -> n') :
    MatrixStep R m n -> MatrixStep R m' n'
  | .row op => .row (mapRowOperation fm op)
  | .col op => .col (mapColumnOperation fn op)


def mapLog {m m' n n' R : Type _} (fm : m -> m') (fn : n -> n') :
    OperationLog R m n -> OperationLog R m' n'
  | [] => []
  | step :: log => mapStep fm fn step :: mapLog fm fn log


theorem isRowStep_mapStep {m m' n n' R : Type _} (fm : m -> m') (fn : n -> n')
    (step : MatrixStep R m n) :
    IsRowStep (mapStep fm fn step) ↔ IsRowStep step := by
  cases step <;> rfl


theorem unimodularStep_mapStep {m m' n n' R : Type _} [CommRing R] [NormalizationMonoid R]
    {fm : m -> m'} {fn : n -> n'}
    (hfm : Function.Injective fm) (hfn : Function.Injective fn)
    (step : MatrixStep R m n) :
    UnimodularStep (mapStep fm fn step) ↔ UnimodularStep step := by
  cases step with
  | row op =>
      cases op with
      | swap i j =>
          simp [mapStep, mapRowOperation, UnimodularStep, UnimodularRowOperation]
      | add src dst c =>
          simpa [mapStep, mapRowOperation, UnimodularStep, UnimodularRowOperation] using
            not_congr hfm.eq_iff
      | smul i c =>
          simp [mapStep, mapRowOperation, UnimodularStep, UnimodularRowOperation]
  | col op =>
      cases op with
      | swap i j =>
          simp [mapStep, mapColumnOperation, UnimodularStep, UnimodularColumnOperation]
      | add src dst c =>
          simpa [mapStep, mapColumnOperation, UnimodularStep, UnimodularColumnOperation] using
            not_congr hfn.eq_iff
      | smul i c =>
          simp [mapStep, mapColumnOperation, UnimodularStep, UnimodularColumnOperation]


theorem mapLog_rowLog {m m' n n' R : Type _} (fm : m -> m') (fn : n -> n')
    (log : OperationLog R m n) (hlog : log.Forall IsRowStep) :
    (mapLog fm fn log).Forall IsRowStep := by
  induction log with
  | nil =>
      simp [mapLog]
  | cons step log ih =>
      have hpair : IsRowStep step ∧ log.Forall IsRowStep := by
        simpa [List.Forall] using hlog
      simp [mapLog, isRowStep_mapStep, hpair.1, ih, hpair.2]


theorem mapLog_unimodular {m m' n n' R : Type _} [CommRing R] [NormalizationMonoid R]
    {fm : m -> m'} {fn : n -> n'}
    (hfm : Function.Injective fm) (hfn : Function.Injective fn)
    (log : OperationLog R m n) (hlog : log.Forall UnimodularStep) :
    (mapLog fm fn log).Forall UnimodularStep := by
  induction log with
  | nil =>
      simp [mapLog]
  | cons step log ih =>
      have hpair : UnimodularStep step ∧ log.Forall UnimodularStep := by
        simpa [List.Forall] using hlog
      simp [mapLog, unimodularStep_mapStep hfm hfn, hpair.1, ih, hpair.2]


def liftColsSucc {m n : Nat} {R : Type _} :
    OperationLog R (Fin m) (Fin n) -> OperationLog R (Fin m) (Fin (n + 1)) :=
  mapLog id Fin.succ


def liftRowsColsSucc {m n : Nat} {R : Type _} :
    OperationLog R (Fin m) (Fin n) -> OperationLog R (Fin (m + 1)) (Fin (n + 1)) :=
  mapLog Fin.succ Fin.succ


@[simp] theorem tailCols_applyRowOperation {m n : Nat} {R : Type _}
    [DecidableEq (Fin m)] [Add R] [Mul R]
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) R) (op : RowOperation R (Fin m)) :
    tailCols (applyRowOperation A op) = applyRowOperation (tailCols A) op := by
  ext i j
  cases op <;> simp [tailCols, applyRowOperation]


@[simp] theorem lowerRight_applyRowOperation_lift {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 1))] [DecidableEq (Fin m)] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (op : RowOperation R (Fin m)) :
    lowerRight (applyRowOperation A (mapRowOperation Fin.succ op)) =
      applyRowOperation (lowerRight A) op := by
  ext i j
  cases op <;> simp [lowerRight, applyRowOperation, mapRowOperation]


theorem replayLog_tailCols_liftColsSucc {m n : Nat} {R : Type _}
    [DecidableEq (Fin m)] [DecidableEq (Fin (n + 1))] [DecidableEq (Fin n)] [Add R] [Mul R]
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) R)
    (log : OperationLog R (Fin m) (Fin n)) (hrow : log.Forall IsRowStep) :
    tailCols (replayLog A (liftColsSucc log)) = replayLog (tailCols A) log := by
  induction log generalizing A with
  | nil =>
      simp [liftColsSucc, mapLog]
  | cons step rest ih =>
      have hpair : IsRowStep step ∧ rest.Forall IsRowStep := by
        simpa [List.Forall] using hrow
      cases step with
      | row op =>
          rw [liftColsSucc, mapLog, replayLog_cons, replayLog_cons]
          cases op with
          | swap i j =>
              simpa [liftColsSucc, applyStep, mapStep, mapRowOperation] using
                ih (applyRowOperation A (.swap i j)) hpair.2
          | add src dst c =>
              simpa [liftColsSucc, applyStep, mapStep, mapRowOperation] using
                ih (applyRowOperation A (.add src dst c)) hpair.2
          | smul i c =>
              simpa [liftColsSucc, applyStep, mapStep, mapRowOperation] using
                ih (applyRowOperation A (.smul i c)) hpair.2
      | col op =>
          cases hpair.1


theorem replayLog_lowerRight_liftRowsColsSucc {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 1))] [DecidableEq (Fin (n + 1))] [DecidableEq (Fin m)] [DecidableEq (Fin n)]
    [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (log : OperationLog R (Fin m) (Fin n)) (hrow : log.Forall IsRowStep) :
    lowerRight (replayLog A (liftRowsColsSucc log)) = replayLog (lowerRight A) log := by
  induction log generalizing A with
  | nil =>
      simp [liftRowsColsSucc, mapLog]
  | cons step rest ih =>
      have hpair : IsRowStep step ∧ rest.Forall IsRowStep := by
        simpa [List.Forall] using hrow
      cases step with
      | row op =>
          rw [liftRowsColsSucc, mapLog, replayLog_cons, replayLog_cons]
          cases op with
          | swap i j =>
              calc
                lowerRight (replayLog (applyRowOperation A (.swap i.succ j.succ)) (mapLog Fin.succ Fin.succ rest))
                    = replayLog (lowerRight (applyRowOperation A (.swap i.succ j.succ))) rest :=
                        ih (applyRowOperation A (.swap i.succ j.succ)) hpair.2
                _ = replayLog (applyRowOperation (lowerRight A) (.swap i j)) rest := by
                      simpa [mapRowOperation] using
                        congrArg (fun M => replayLog M rest)
                          (lowerRight_applyRowOperation_lift A (.swap i j))
          | add src dst c =>
              calc
                lowerRight (replayLog (applyRowOperation A (.add src.succ dst.succ c)) (mapLog Fin.succ Fin.succ rest))
                    = replayLog (lowerRight (applyRowOperation A (.add src.succ dst.succ c))) rest :=
                        ih (applyRowOperation A (.add src.succ dst.succ c)) hpair.2
                _ = replayLog (applyRowOperation (lowerRight A) (.add src dst c)) rest := by
                      simpa [mapRowOperation] using
                        congrArg (fun M => replayLog M rest)
                          (lowerRight_applyRowOperation_lift A (.add src dst c))
          | smul i c =>
              calc
                lowerRight (replayLog (applyRowOperation A (.smul i.succ c)) (mapLog Fin.succ Fin.succ rest))
                    = replayLog (lowerRight (applyRowOperation A (.smul i.succ c))) rest :=
                        ih (applyRowOperation A (.smul i.succ c)) hpair.2
                _ = replayLog (applyRowOperation (lowerRight A) (.smul i c)) rest := by
                      simpa [mapRowOperation] using
                        congrArg (fun M => replayLog M rest)
                          (lowerRight_applyRowOperation_lift A (.smul i c))
      | col op =>
          cases hpair.1


def diagLiftMatrix {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) :
    _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun i j =>
    Fin.cases
      (Fin.cases (1 : R) (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => U i' j') j)
      i


@[simp] theorem diagLiftMatrix_zero_zero {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) :
    diagLiftMatrix U 0 0 = 1 := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_zero_succ {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) (j : Fin m) :
    diagLiftMatrix U 0 j.succ = 0 := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_succ_zero {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) (i : Fin m) :
    diagLiftMatrix U i.succ 0 = 0 := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_succ_succ {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    diagLiftMatrix U i.succ j.succ = U i j := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_one {m : Nat} {R : Type _} [CommRing R] :
    diagLiftMatrix (1 : _root_.Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [diagLiftMatrix, _root_.Matrix.one_apply]
      | succ j =>
          have h : (0 : Fin (m + 1)) ≠ j.succ := by
            intro hEq
            exact Fin.succ_ne_zero j hEq.symm
          simp [diagLiftMatrix, _root_.Matrix.one_apply, h]
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have h : (i.succ : Fin (m + 1)) ≠ 0 := by simp
          simp [diagLiftMatrix, _root_.Matrix.one_apply, h]
      | succ j =>
          simp [diagLiftMatrix, _root_.Matrix.one_apply]


@[simp] theorem diagLiftMatrix_mul {m : Nat} {R : Type _}
    [CommRing R]
    (U V : _root_.Matrix (Fin m) (Fin m) R) :
    diagLiftMatrix U * diagLiftMatrix V = diagLiftMatrix (U * V) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases <;>
        simp [diagLiftMatrix, _root_.Matrix.mul_apply, Fin.sum_univ_succ]
  | succ i =>
      cases j using Fin.cases <;>
        simp [diagLiftMatrix, _root_.Matrix.mul_apply, Fin.sum_univ_succ]


theorem unimodular_diagLiftMatrix {m : Nat} {R : Type _} [CommRing R]
    {U : _root_.Matrix (Fin m) (Fin m) R} (hU : Unimodular U) :
    Unimodular (diagLiftMatrix U) := by
  have hmul : diagLiftMatrix U * diagLiftMatrix U⁻¹ = 1 := by
    calc
      diagLiftMatrix U * diagLiftMatrix U⁻¹ = diagLiftMatrix (U * U⁻¹) := by
        simpa using diagLiftMatrix_mul U U⁻¹
      _ = diagLiftMatrix (1 : _root_.Matrix (Fin m) (Fin m) R) := by
        rw [_root_.Matrix.mul_nonsing_inv _ hU]
      _ = 1 := diagLiftMatrix_one
  have hmul' : diagLiftMatrix U⁻¹ * diagLiftMatrix U = 1 := by
    calc
      diagLiftMatrix U⁻¹ * diagLiftMatrix U = diagLiftMatrix (U⁻¹ * U) := by
        simpa using diagLiftMatrix_mul U⁻¹ U
      _ = diagLiftMatrix (1 : _root_.Matrix (Fin m) (Fin m) R) := by
        rw [_root_.Matrix.nonsing_inv_mul _ hU]
      _ = 1 := diagLiftMatrix_one
  have hUnit : IsUnit (diagLiftMatrix U) := by
    exact ⟨⟨diagLiftMatrix U, diagLiftMatrix U⁻¹, hmul, hmul'⟩, rfl⟩
  exact (_root_.Matrix.isUnit_iff_isUnit_det (A := diagLiftMatrix U)).1 hUnit


@[simp] theorem diagLiftMatrix_mul_topRow {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin (m + 1)) (Fin n) R) :
    (diagLiftMatrix U * A) 0 = A 0 := by
  ext j
  simp [diagLiftMatrix, _root_.Matrix.mul_apply, Fin.sum_univ_succ]


@[simp] theorem lowerRight_diagLiftMatrix_mul {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) :
    lowerRight (diagLiftMatrix U * A) = U * lowerRight A := by
  ext i j
  simp [diagLiftMatrix, lowerRight, _root_.Matrix.mul_apply, Fin.sum_univ_succ]


private def topLiftMatrix {m : Nat} {R : Type _} [Zero R]
    (B : _root_.Matrix (Fin 2) (Fin 2) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) :
    _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  fun i j =>
    Fin.cases
      (Fin.cases (B 0 0)
        (fun j' => Fin.cases (B 0 1) (fun _ => 0) j')
        j)
      (fun i' =>
        Fin.cases
          (Fin.cases (B 1 0)
            (fun j' => Fin.cases (B 1 1) (fun _ => 0) j')
            j)
          (fun i'' =>
            Fin.cases 0
              (fun j' => Fin.cases 0 (fun j'' => U i'' j'') j')
              j)
          i')
      i


def topBezoutMatrix {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) : _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  topLiftMatrix (bezoutReductionMatrix a b) 1


private noncomputable def topBezoutMatrixInv {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    R -> R -> _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  fun a b => topLiftMatrix (bezoutReductionMatrix a b)⁻¹ 1


@[simp] theorem topBezoutMatrix_zero_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 0 0 = bezoutReductionMatrix a b 0 0 := by
  rfl


@[simp] theorem topBezoutMatrix_zero_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 0 1 = bezoutReductionMatrix a b 0 1 := by
  rfl


@[simp] theorem topBezoutMatrix_one_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 1 0 = bezoutReductionMatrix a b 1 0 := by
  rfl


@[simp] theorem topBezoutMatrix_one_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 1 1 = bezoutReductionMatrix a b 1 1 := by
  rfl


@[simp] theorem topBezoutMatrix_zero_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrix (m := m) a b 0 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_one_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrix (m := m) a b 1 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ 0 = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ 1 = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i j : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 0 0 = (bezoutReductionMatrix a b)⁻¹ 0 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 0 1 = (bezoutReductionMatrix a b)⁻¹ 0 1 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 1 0 = (bezoutReductionMatrix a b)⁻¹ 1 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 1 1 = (bezoutReductionMatrix a b)⁻¹ 1 1 := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrixInv (m := m) a b 0 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrixInv (m := m) a b 1 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ 0 = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ 1 = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i j : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
  rfl


private theorem topBezoutMatrix_mul_inv_topBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M 0 0 = 1 ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = 1 := by
  have hBezout : Unimodular (bezoutReductionMatrix a b) := by
    simpa [Unimodular, det_bezoutReductionMatrix]
  have hMulTop : bezoutReductionMatrix a b * (bezoutReductionMatrix a b)⁻¹ = 1 := by
    exact _root_.Matrix.mul_nonsing_inv _ hBezout
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 0) 0
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 0) 1
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 1) 0
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 1) 1


private theorem topBezoutMatrix_mul_inv_offDiag {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M 0 j.succ.succ = 0 ∧ M 1 j.succ.succ = 0 ∧
      M j.succ.succ 0 = 0 ∧ M j.succ.succ 1 = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]


private theorem topBezoutMatrix_mul_inv_unitBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i j : Fin m) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M i.succ.succ j.succ.succ = (1 : _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R) i.succ.succ j.succ.succ := by
  have hTail :
      ((1 : _root_.Matrix (Fin m) (Fin m) R) * (1 : _root_.Matrix (Fin m) (Fin m) R)) i j =
        (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
    simpa using congrFun
      (congrFun
        (show (1 : _root_.Matrix (Fin m) (Fin m) R) * (1 : _root_.Matrix (Fin m) (Fin m) R) =
            (1 : _root_.Matrix (Fin m) (Fin m) R) by simp) i) j
  dsimp
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simpa [_root_.Matrix.one_apply] using hTail


theorem topBezoutMatrix_mul_inv {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).1
      | succ j =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).2.1
          | succ j =>
              exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b j).1
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).2.2.1
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).2.2.2
              | succ j =>
                  exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b j).2.1
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b i).2.2.1
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b i).2.2.2
              | succ j =>
                  exact topBezoutMatrix_mul_inv_unitBlock (m := m) a b i j


theorem unimodular_topBezoutMatrix {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) : Unimodular (topBezoutMatrix (m := m) a b) := by
  simpa [Unimodular] using
    (_root_.Matrix.isUnit_det_of_right_inverse
      (A := topBezoutMatrix (m := m) a b)
      (B := topBezoutMatrixInv (m := m) a b)
      (topBezoutMatrix_mul_inv (m := m) a b))


theorem topBezoutMatrix_mul_apply_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) 0 j =
      bezoutReductionMatrix a b 0 0 * A 0 j +
        bezoutReductionMatrix a b 0 1 * A 1 j := by
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [topBezoutMatrix_zero_zero, topBezoutMatrix_zero_one, topBezoutMatrix_zero_succ_succ]


theorem topBezoutMatrix_mul_apply_one {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) 1 j =
      bezoutReductionMatrix a b 1 0 * A 0 j +
        bezoutReductionMatrix a b 1 1 * A 1 j := by
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [topBezoutMatrix_one_zero, topBezoutMatrix_one_one, topBezoutMatrix_one_succ_succ]


theorem topBezoutMatrix_mul_apply_succ_succ {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin m) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) i.succ.succ j = A i.succ.succ j := by
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [topBezoutMatrix_succ_succ_zero, topBezoutMatrix_succ_succ_one,
    topBezoutMatrix_succ_succ_succ_succ, _root_.Matrix.one_apply]


theorem Bezout_preserves_zeros {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) (i : Fin m)
    (h : A i.succ.succ 0 = 0) :
    (topBezoutMatrix (m := m) a b * A) i.succ.succ 0 = 0 := by
  rw [topBezoutMatrix_mul_apply_succ_succ (m := m) (n := n + 1) (a := a) (b := b)
    (A := A) i (0 : Fin (n + 1))]
  exact h


theorem topBezoutMatrix_mul_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) :
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 0 0 =
      EuclideanDomain.gcd (A 0 0) (A 1 0) := by
  have hvec := bezoutReductionMatrix_mulVec (A 0 0) (A 1 0)
  calc
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 0 0
        = bezoutReductionMatrix (A 0 0) (A 1 0) 0 0 * A 0 0 +
            bezoutReductionMatrix (A 0 0) (A 1 0) 0 1 * A 1 0 :=
          topBezoutMatrix_mul_apply_zero (m := m) (n := n + 1) (A 0 0) (A 1 0) A
            (0 : Fin (n + 1))
    _ = EuclideanDomain.gcd (A 0 0) (A 1 0) := by
          simpa [_root_.Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hvec 0


theorem topBezoutMatrix_mul_rowOneFirstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) :
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 1 0 = 0 := by
  have hvec := bezoutReductionMatrix_mulVec (A 0 0) (A 1 0)
  calc
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 1 0
        = bezoutReductionMatrix (A 0 0) (A 1 0) 1 0 * A 0 0 +
            bezoutReductionMatrix (A 0 0) (A 1 0) 1 1 * A 1 0 :=
          topBezoutMatrix_mul_apply_one (m := m) (n := n + 1) (A 0 0) (A 1 0) A
            (0 : Fin (n + 1))
    _ = 0 := by
          simpa [_root_.Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hvec 1


def LeftTransform.diagLift {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) (hU : Unimodular U) :
    LeftTransform A :=
  { U := diagLiftMatrix U
    B := diagLiftMatrix U * A
    left_mul := by rfl
    unimodular := unimodular_diagLiftMatrix hU }


def LeftTransform.topBezout {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) : LeftTransform A :=
  { U := topBezoutMatrix (m := m) (A 0 0) (A 1 0)
    B := topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A
    left_mul := by rfl
    unimodular := unimodular_topBezoutMatrix (m := m) (A 0 0) (A 1 0) }

structure HNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  H : _root_.Matrix m n R
  left_mul : U * A = H
  isHermite : IsHermiteNormalForm H

theorem firstNonzero?_eq_none {R : Type _} [Zero R] [DecidableEq R] :
    {n : Nat} -> (row : Fin n -> R) -> firstNonzero? row = none -> ∀ i, row i = 0
  | 0, _, _, i => Fin.elim0 i
  | _ + 1, row, hnone, i => by
      by_cases h0 : row 0 = 0
      · rw [firstNonzero?, h0] at hnone
        cases htail : firstNonzero? (fun j => row j.succ) with
        | none =>
            cases i using Fin.cases with
            | zero =>
                exact h0
            | succ j =>
                exact firstNonzero?_eq_none (fun k => row k.succ) htail j
        | some j =>
            simp [htail] at hnone
      · exfalso
        simp [firstNonzero?, h0] at hnone


theorem firstNonzero?_some_ne_zero {R : Type _} [Zero R] [DecidableEq R] :
    {n : Nat} -> (row : Fin n -> R) -> {i : Fin n} -> firstNonzero? row = some i -> row i ≠ 0
  | 0, _, i, _ => Fin.elim0 i
  | _ + 1, row, i, hsome => by
      by_cases h0 : row 0 = 0
      · rw [firstNonzero?, h0] at hsome
        cases i using Fin.cases with
        | zero =>
            simp at hsome
        | succ j =>
            cases htail : firstNonzero? (fun k => row k.succ) with
            | none =>
                simp [htail] at hsome
            | some j' =>
                simp [htail] at hsome
                subst hsome
                exact firstNonzero?_some_ne_zero (fun k => row k.succ) htail
      · cases i using Fin.cases with
        | zero =>
            exact h0
        | succ j =>
            have hsome0 : firstNonzero? row = some (0 : Fin (_ + 1)) := by
              simp [firstNonzero?, h0]
            have hzero : (0 : Fin (_ + 1)) = j.succ := by
              simpa using hsome0.symm.trans hsome
            have : False := by
              cases hzero
            exact False.elim this


theorem firstNonzero?_some_eq_zero_of_lt {R : Type _} [Zero R] [DecidableEq R] :
    {n : Nat} -> (row : Fin n -> R) -> {i : Fin n} ->
      firstNonzero? row = some i -> ∀ j : Fin n, j < i -> row j = 0
  | 0, _, i, hsome, j, _ => Fin.elim0 i
  | _ + 1, row, i, hsome, j, hj => by
      by_cases h0 : row 0 = 0
      · rw [firstNonzero?, h0] at hsome
        cases i using Fin.cases with
        | zero =>
            simp at hsome
        | succ i' =>
            cases j using Fin.cases with
            | zero =>
                exact h0
            | succ j' =>
                cases htail : firstNonzero? (fun k => row k.succ) with
                | none =>
                    simp [htail] at hsome
                | some k =>
                    simp [htail] at hsome
                    subst hsome
                    exact firstNonzero?_some_eq_zero_of_lt (fun k => row k.succ) htail j'
                      (Fin.succ_lt_succ_iff.mp hj)
      · cases i using Fin.cases with
        | zero =>
            exact False.elim (Nat.not_lt_zero _ hj)
        | succ i' =>
            have hsome0 : firstNonzero? row = some (0 : Fin (_ + 1)) := by
              simp [firstNonzero?, h0]
            have : False := by
              have hEq : (0 : Fin (_ + 1)) = i'.succ := by
                simpa using hsome0.symm.trans hsome
              cases hEq
            exact False.elim this


@[simp] theorem firstNonzero?_zero {n : Nat} {R : Type _} [Zero R] [DecidableEq R] :
    firstNonzero? (fun _ : Fin n => (0 : R)) = none := by
  induction n with
  | zero =>
      simp [firstNonzero?]
  | succ n ih =>
      simp [firstNonzero?, ih]


@[simp] theorem tailCols_mul {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) R) :
    tailCols (U * A) = U * tailCols A := by
  ext i j
  simp [tailCols, _root_.Matrix.mul_apply]


theorem firstCol_zero_mul {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) R)
    (hzero : ∀ i, A i 0 = 0) :
    ∀ i, (U * A) i 0 = 0 := by
  intro i
  simp [_root_.Matrix.mul_apply, hzero]


theorem unimodular_reindex {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (e : m ≃ n) {U : _root_.Matrix m m R} (hU : Unimodular U) :
    Unimodular (_root_.Matrix.reindex e e U) := by
  simpa [Unimodular, _root_.Matrix.det_reindex_self] using hU


@[simp] theorem lowerRight_applyRowOperation_addToTop {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 1))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin m) (c : R) :
    lowerRight (applyRowOperation A (.add i.succ 0 c)) = lowerRight A := by
  ext r s
  simp [lowerRight, applyRowOperation]


@[simp] theorem applyRowOperation_addToTop_succ {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 1))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i j : Fin m) (c : R) :
    applyRowOperation A (.add i.succ 0 c) j.succ = A j.succ := by
  ext s
  simp [applyRowOperation]


theorem hnf_rowBelow_zero_at_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} (hA : IsHermiteNormalFormFin A) :
    ∀ {i j : Fin m} (hij : i < j) {p : Fin n},
      firstNonzero? (fun k : Fin n => A i k) = some p -> A j p = 0 := by
  induction hA with
  | emptyRows A =>
      intro i
      exact Fin.elim0 i
  | emptyCols A =>
      intro i j hij p
      exact Fin.elim0 p
  | zeroCol A hzero hTail ih =>
      intro i j hij p hsome
      cases p using Fin.cases with
      | zero =>
          have h0i := hzero i
          simp [firstNonzero?, h0i] at hsome
      | succ p =>
          have h0i := hzero i
          rw [firstNonzero?, h0i] at hsome
          cases htaili : firstNonzero? (fun k : Fin _ => A i k.succ) with
          | none =>
              simp [htaili] at hsome
          | some q =>
              simp [htaili] at hsome
              subst hsome
              exact ih hij htaili
  | pivot A hpivot hnorm hbelow hLower hreduced ih =>
      intro i j hij p hsome
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (lt_irrefl _ hij)
          | succ j =>
              have hp : 0 = p := by
                simpa [firstNonzero?, hpivot] using hsome
              subst hp
              exact hbelow j
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (Nat.not_lt_zero _ hij)
          | succ j =>
              have hij' : i < j := Fin.succ_lt_succ_iff.mp hij
              cases p using Fin.cases with
              | zero =>
                  have h0i := hbelow i
                  simp [firstNonzero?, h0i] at hsome
              | succ p =>
                  have h0i := hbelow i
                  rw [firstNonzero?, h0i] at hsome
                  cases htaili : firstNonzero? (fun k : Fin _ => A i.succ k.succ) with
                  | none =>
                      simp [htaili] at hsome
                  | some q =>
                      simp [htaili] at hsome
                      subst hsome
                      exact ih hij' htaili


@[simp] theorem applyRowOperation_swap_succ_one_top {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin (m + 1)) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) 0 = A 0 := by
  ext j
  have h0i : ¬ (0 : Fin (m + 2)) = i.succ := by
    intro hEq
    exact Fin.succ_ne_zero i hEq.symm
  have h01 : (0 : Fin (m + 2)) ≠ (1 : Fin (m + 2)) := by simp
  simp [applyRowOperation, h0i, h01]


@[simp] theorem applyRowOperation_swap_succ_one_rowOne {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin (m + 1)) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) 1 = A i.succ := by
  cases i using Fin.cases with
  | zero =>
      ext j
      simp [applyRowOperation]
  | succ i =>
      ext j
      have hne : (1 : Fin (m + 2)) ≠ i.succ.succ := by
        intro hEq
        have hval : (1 : Nat) = i.1.succ.succ := by
          simpa using congrArg Fin.val hEq
        simp at hval
      simp [applyRowOperation, hne]


@[simp] theorem applyRowOperation_swap_succ_one_target {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin (m + 1)) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) i.succ = A 1 := by
  ext j
  simp [applyRowOperation]


@[simp] theorem applyRowOperation_swap_succ_one_other {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i j : Fin (m + 1))
    (hj0 : j ≠ 0) (hji : j ≠ i) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) j.succ = A j.succ := by
  ext s
  have hjeq1 : (j.succ : Fin (m + 2)) ≠ 1 := by
    intro h
    apply hj0
    apply Fin.ext
    exact Nat.succ.inj <| by simpa using congrArg Fin.val h
  have hjeqi : j.succ ≠ i.succ := by
    intro h
    apply hji
    apply Fin.ext
    exact Nat.succ.inj <| by simpa using congrArg Fin.val h
  simp [applyRowOperation, hjeqi, hjeq1]


private theorem zeroHermite {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
    IsHermiteNormalFormFin (0 : _root_.Matrix (Fin m) (Fin n) R) := by
  induction n generalizing m with
  | zero =>
      exact IsHermiteNormalFormFin.emptyCols _
  | succ n ih =>
      cases m with
      | zero =>
          exact IsHermiteNormalFormFin.emptyRows _
      | succ m =>
          refine IsHermiteNormalFormFin.zeroCol _ ?_ ?_
          · intro i
            simp
          · simpa [tailCols] using (ih (m := m + 1))


namespace Internal

structure FinHNFResult {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) where
  U : _root_.Matrix (Fin m) (Fin m) R
  H : _root_.Matrix (Fin m) (Fin n) R
  left_mul : U * A = H
  unimodular : Unimodular U
  isHermite : IsHermiteNormalFormFin H


def clearFirstColumnStep {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) : LeftTransform A :=
  if hzero : t.B i.succ 0 = 0 then
    t
  else
    let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)


def clearFirstColumnLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ m + 1 -> LeftTransform A -> LeftTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      clearFirstColumnStep i t'


def topReductionCoeff {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) (i : Fin (m + 1)) (j : Fin n) : R :=
  -(A 0 j.succ / A i.succ j.succ)


def reduceTopRowStep {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) : LeftTransform A :=
  match hrow : firstNonzero? (fun j : Fin n => t.B i.succ j.succ) with
  | none => t
  | some j =>
      t.trans <|
        LeftTransform.add t.B i.succ 0 (topReductionCoeff t.B i j) (by simp)


def reduceTopRowLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ m + 1 -> LeftTransform A -> LeftTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let t' := reduceTopRowLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      reduceTopRowStep i t'


theorem applyRowOperation_reduceTop_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R)
    (i : Fin (m + 1)) (j : Fin n) :
    applyRowOperation A (.add i.succ 0 (topReductionCoeff A i j)) 0 j.succ =
      A 0 j.succ % A i.succ j.succ := by
  simpa [applyRowOperation, topReductionCoeff, EuclideanDomain.mod_eq_sub_mul_div, sub_eq_add_neg,
    mul_comm, mul_left_comm, mul_assoc]


theorem clearFirstColumnStep_topLeft_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) (htop : t.B 0 0 ≠ 0) :
    (clearFirstColumnStep i t).B 0 0 ≠ 0 := by
  by_cases hzero : t.B i.succ 0 = 0
  · simp [clearFirstColumnStep, hzero, htop]
  · let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    let tNorm := tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)
    have htop' : tSwap.B 0 0 = t.B 0 0 := by
      simp [tSwap, LeftTransform.swap, LeftTransform.trans]
    have hrow' : tSwap.B 1 0 = t.B i.succ 0 := by
      simp [tSwap, LeftTransform.swap, LeftTransform.trans]
    have hdet :
        tBez.B 0 0 =
          EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) := by
      calc
        tBez.B 0 0 = EuclideanDomain.gcd (tSwap.B 0 0) (tSwap.B 1 0) := by
          simpa [tBez, LeftTransform.topBezout, LeftTransform.trans] using
            topBezoutMatrix_mul_topLeft (m := m) (n := n) (A := tSwap.B)
        _ = EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) := by
          rw [htop', hrow']
    have hnormTop :
        tNorm.B 0 0 = normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
      calc
        tNorm.B 0 0 = normalize (tBez.B 0 0) := by
          simp [tNorm, LeftTransform.unitSmul, LeftTransform.trans, applyRowOperation,
            normalize_apply, mul_comm]
        _ = normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
          rw [hdet]
    have hgcdNe : EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) ≠ 0 := by
      intro hg
      exact htop ((EuclideanDomain.gcd_eq_zero_iff.mp hg).1)
    have hclear : clearFirstColumnStep i t = tNorm := by
      simp [clearFirstColumnStep, hzero, tNorm, tBez, tSwap]
    rw [hclear, hnormTop]
    exact fun hg => hgcdNe (normalize_eq_zero.mp hg)


theorem clearFirstColumnStep_topLeft_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A)
    (hnorm : t.B 0 0 = normalize (t.B 0 0)) :
    (clearFirstColumnStep i t).B 0 0 = normalize ((clearFirstColumnStep i t).B 0 0) := by
  by_cases hzero : t.B i.succ 0 = 0
  · simpa [clearFirstColumnStep, hzero] using hnorm
  · let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    let tNorm := tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)
    have hnormTop : tNorm.B 0 0 = normalize (tBez.B 0 0) := by
      simp [tNorm, LeftTransform.unitSmul, LeftTransform.trans, applyRowOperation,
        normalize_apply, mul_comm]
    have hclear : clearFirstColumnStep i t = tNorm := by
      simp [clearFirstColumnStep, hzero, tNorm, tBez, tSwap]
    rw [hclear, hnormTop]
    simpa using (normalize_idem (tBez.B 0 0)).symm


theorem clearFirstColumnStep_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A)
    (hprefix : ∀ j : Fin (m + 1), j.1 < i.1 -> t.B j.succ 0 = 0) :
    ∀ j : Fin (m + 1), j.1 < i.1.succ -> (clearFirstColumnStep i t).B j.succ 0 = 0 := by
  intro j hj
  by_cases hzero : t.B i.succ 0 = 0
  · have hj' : j.1 < i.1 ∨ j.1 = i.1 := by
      exact Nat.lt_succ_iff_lt_or_eq.mp hj
    rcases hj' with hj' | hEq
    · simpa [clearFirstColumnStep, hzero] using hprefix j hj'
    · have : j = i := Fin.ext hEq
      subst this
      simpa [clearFirstColumnStep, hzero]
  · let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    let tNorm := tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)
    have hbelowEq (r : Fin (m + 1)) : tNorm.B r.succ 0 = tBez.B r.succ 0 := by
      simp [tNorm, LeftTransform.unitSmul, LeftTransform.trans, applyRowOperation]
    have hclear : clearFirstColumnStep i t = tNorm := by
      simp [clearFirstColumnStep, hzero, tNorm, tBez, tSwap]
    have hrowOneZero : tBez.B 1 0 = 0 := by
      simpa [tBez, tSwap, LeftTransform.topBezout, LeftTransform.trans] using
        topBezoutMatrix_mul_rowOneFirstCol (m := m) (n := n) (A := tSwap.B)
    have hj' : j.1 < i.1 ∨ j.1 = i.1 := by
      exact Nat.lt_succ_iff_lt_or_eq.mp hj
    rcases hj' with hj' | hEq
    · cases j using Fin.cases with
      | zero =>
          calc
            (clearFirstColumnStep i t).B 1 0 = tNorm.B 1 0 := by simpa [hclear]
            _ = tBez.B 1 0 := hbelowEq 0
            _ = 0 := hrowOneZero
      | succ j =>
          have hswapEq : tSwap.B j.succ.succ 0 = t.B j.succ.succ 0 := by
            simpa [tSwap, LeftTransform.swap, LeftTransform.trans] using
              congrFun
                (applyRowOperation_swap_succ_one_other t.B i j.succ (by simp)
                  (ne_of_lt hj')) 0
          have hswapZero : tSwap.B j.succ.succ 0 = 0 := by
            rw [hswapEq]
            exact hprefix j.succ hj'
          have hbezoutZero : tBez.B j.succ.succ 0 = 0 := by
            simpa [tBez, tSwap, LeftTransform.topBezout, LeftTransform.trans] using
              (Bezout_preserves_zeros (m := m) (n := n) (a := tSwap.B 0 0) (b := tSwap.B 1 0)
                (A := tSwap.B) j hswapZero)
          calc
            (clearFirstColumnStep i t).B j.succ.succ 0 = tNorm.B j.succ.succ 0 := by
              simpa [hclear]
            _ = tBez.B j.succ.succ 0 := hbelowEq j.succ
            _ = 0 := hbezoutZero
    · have : j = i := Fin.ext hEq
      subst j
      cases i using Fin.cases with
      | zero =>
          calc
            (clearFirstColumnStep 0 t).B 1 0 = tNorm.B 1 0 := by simpa [hclear]
            _ = tBez.B 1 0 := hbelowEq 0
            _ = 0 := hrowOneZero
      | succ i =>
          have hrowOneBefore : t.B 1 0 = 0 := by
            exact hprefix 0 (by simpa using i.succ.is_lt)
          have hswapEq : tSwap.B i.succ.succ 0 = t.B 1 0 := by
            simpa [tSwap, LeftTransform.swap, LeftTransform.trans] using
              congrFun (applyRowOperation_swap_succ_one_target t.B i.succ) 0
          have hswapZero : tSwap.B i.succ.succ 0 = 0 := by
            rw [hswapEq]
            exact hrowOneBefore
          have hbezoutZero : tBez.B i.succ.succ 0 = 0 := by
            simpa [tBez, tSwap, LeftTransform.topBezout, LeftTransform.trans] using
              (Bezout_preserves_zeros (m := m) (n := n) (a := tSwap.B 0 0) (b := tSwap.B 1 0)
                (A := tSwap.B) i hswapZero)
          calc
            (clearFirstColumnStep i.succ t).B i.succ.succ 0 = tNorm.B i.succ.succ 0 := by
              simpa [hclear]
            _ = tBez.B i.succ.succ 0 := hbelowEq i.succ
            _ = 0 := hbezoutZero


theorem clearFirstColumnLoop_topLeft_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (htop : t.B 0 0 ≠ 0) :
    (clearFirstColumnLoop k hk t).B 0 0 ≠ 0 := by
  induction k generalizing t with
  | zero =>
      simpa [clearFirstColumnLoop] using htop
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have htop' : t'.B 0 0 ≠ 0 := by
        simpa [t', hk'] using ih hk' t htop
      simpa [clearFirstColumnLoop, hk', t'] using
        clearFirstColumnStep_topLeft_ne_zero i t' htop'


theorem clearFirstColumnLoop_topLeft_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hnorm : t.B 0 0 = normalize (t.B 0 0)) :
    (clearFirstColumnLoop k hk t).B 0 0 = normalize ((clearFirstColumnLoop k hk t).B 0 0) := by
  induction k generalizing t with
  | zero =>
      simpa [clearFirstColumnLoop] using hnorm
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        simpa [t', hk'] using ih hk' t hnorm
      simpa [clearFirstColumnLoop, hk', t'] using
        clearFirstColumnStep_topLeft_normalized i t' hnorm'


theorem clearFirstColumnLoop_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A) :
    ∀ j : Fin (m + 1), j.1 < k -> (clearFirstColumnLoop k hk t).B j.succ 0 = 0 := by
  induction k generalizing t with
  | zero =>
      intro j hj
      exact False.elim (Nat.not_lt_zero _ hj)
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      intro j hj
      have hprefix : ∀ j' : Fin (m + 1), j'.1 < i.1 -> t'.B j'.succ 0 = 0 := by
        intro j' hj'
        simpa [t', hk'] using ih hk' t j' hj'
      simpa [clearFirstColumnLoop, hk', t'] using
        clearFirstColumnStep_prefix_zero i t' hprefix j hj


theorem reduceTopRowStep_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) (hzero : t.B i.succ 0 = 0) :
    (reduceTopRowStep i t).B 0 0 = t.B 0 0 := by
  unfold reduceTopRowStep
  cases hrow : firstNonzero? (fun j : Fin n => t.B i.succ j.succ) with
  | none =>
      rfl
  | some j =>
      simp [hrow, LeftTransform.add, LeftTransform.trans,
        applyRowOperation, topReductionCoeff, hzero]


theorem reduceTopRowStep_lowerRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i j : Fin (m + 1)) (t : LeftTransform A) :
    (reduceTopRowStep i t).B j.succ = t.B j.succ := by
  unfold reduceTopRowStep
  cases hrow : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) with
  | none =>
      rfl
  | some p =>
      ext s
      simp [hrow, LeftTransform.add, LeftTransform.trans, applyRowOperation]


theorem reduceTopRowStep_topEntry_eq_of_source_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) (c : Fin (n + 1))
    (hsrc : t.B i.succ c = 0) :
    (reduceTopRowStep i t).B 0 c = t.B 0 c := by
  unfold reduceTopRowStep
  cases hrow : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) with
  | none =>
      rfl
  | some p =>
      simp [hrow, LeftTransform.add, LeftTransform.trans,
        applyRowOperation, topReductionCoeff, hsrc]


theorem reduceTopRowStep_current_reduced {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) {j : Fin n}
    (hrow : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) = some j) :
    (reduceTopRowStep i t).B 0 j.succ =
      (reduceTopRowStep i t).B 0 j.succ % t.B i.succ j.succ := by
  unfold reduceTopRowStep
  rw [hrow]
  change applyRowOperation t.B (.add i.succ 0 (topReductionCoeff t.B i j)) 0 j.succ =
    applyRowOperation t.B (.add i.succ 0 (topReductionCoeff t.B i j)) 0 j.succ % t.B i.succ j.succ
  rw [applyRowOperation_reduceTop_pivot t.B i j]
  rw [CanonicalMod.mod_mod]


theorem reduceTopRowStep_preserves_reduced {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i r : Fin (m + 1)) (t : LeftTransform A) {q : Fin n}
    (hrow : firstNonzero? (fun s : Fin n => t.B r.succ s.succ) = some q)
    (hreduced : t.B 0 q.succ = t.B 0 q.succ % t.B r.succ q.succ)
    (hsrcZero : t.B i.succ q.succ = 0) :
    (reduceTopRowStep i t).B 0 q.succ =
      (reduceTopRowStep i t).B 0 q.succ % t.B r.succ q.succ := by
  have htop := reduceTopRowStep_topEntry_eq_of_source_zero i t q.succ hsrcZero
  have hrowEq : (reduceTopRowStep i t).B r.succ q.succ = t.B r.succ q.succ := by
    exact congrFun (reduceTopRowStep_lowerRow i r t) q.succ
  simpa [htop, hrowEq] using hreduced


theorem reduceTopRowLoop_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A) :
    lowerRight (reduceTopRowLoop k hk t).B = lowerRight t.B := by
  induction k generalizing t with
  | zero =>
      simp [reduceTopRowLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      change lowerRight (reduceTopRowStep i t').B = lowerRight t.B
      cases hrow : firstNonzero? (fun s : Fin n => t'.B i.succ s.succ) with
      | none =>
          unfold reduceTopRowStep
          rw [hrow]
          simpa [t'] using ih hk' t
      | some p =>
          unfold reduceTopRowStep
          rw [hrow]
          simpa [LeftTransform.add, LeftTransform.trans,
            lowerRight_applyRowOperation_addToTop, t'] using ih hk' t


theorem reduceTopRowLoop_lowerRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A) (j : Fin (m + 1)) :
    (reduceTopRowLoop k hk t).B j.succ = t.B j.succ := by
  induction k generalizing t with
  | zero =>
      simp [reduceTopRowLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      change (reduceTopRowStep i t').B j.succ = t.B j.succ
      calc
        (reduceTopRowStep i t').B j.succ = t'.B j.succ := reduceTopRowStep_lowerRow i j t'
        _ = t.B j.succ := by simpa [t', hk'] using ih hk' t


theorem reduceTopRowLoop_below_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hzero : ∀ i : Fin (m + 1), t.B i.succ 0 = 0) :
    ∀ i : Fin (m + 1), (reduceTopRowLoop k hk t).B i.succ 0 = 0 := by
  induction k generalizing t with
  | zero =>
      intro i
      simp [reduceTopRowLoop, hzero]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hzero' : ∀ j : Fin (m + 1), t'.B j.succ 0 = 0 := by
        simpa [t', hk'] using ih hk' t hzero
      intro j
      change (reduceTopRowStep i t').B j.succ 0 = 0
      rw [show (reduceTopRowStep i t').B j.succ 0 = t'.B j.succ 0 by
        exact congrFun (reduceTopRowStep_lowerRow i j t') 0]
      exact hzero' j


theorem reduceTopRowLoop_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hzero : ∀ i : Fin (m + 1), t.B i.succ 0 = 0) :
    (reduceTopRowLoop k hk t).B 0 0 = t.B 0 0 := by
  induction k generalizing t with
  | zero =>
      simp [reduceTopRowLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hzero' : ∀ j : Fin (m + 1), t'.B j.succ 0 = 0 := by
        simpa [t', hk'] using reduceTopRowLoop_below_zero k hk' t hzero
      change (reduceTopRowStep i t').B 0 0 = t.B 0 0
      calc
        (reduceTopRowStep i t').B 0 0 = t'.B 0 0 := reduceTopRowStep_topLeft i t' (hzero' i)
        _ = t.B 0 0 := by simpa [t', hk'] using ih hk' t hzero


theorem reduceTopRowLoop_reduced_prefix {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hLower : IsHermiteNormalFormFin (lowerRight t.B))
    (hzero : ∀ i : Fin (m + 1), t.B i.succ 0 = 0) :
    ∀ i : Fin (m + 1), i.1 < k ->
      match firstNonzero? (fun s : Fin n => t.B i.succ s.succ) with
      | none => True
      | some j =>
          (reduceTopRowLoop k hk t).B 0 j.succ =
            (reduceTopRowLoop k hk t).B 0 j.succ % t.B i.succ j.succ := by
  induction k generalizing t with
  | zero =>
      intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let iCurr : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hloop : reduceTopRowLoop (k + 1) hk t = reduceTopRowStep iCurr t' := by
        rfl
      have hLowerEq : lowerRight t'.B = lowerRight t.B := by
        simpa [t', hk'] using reduceTopRowLoop_lowerRight k hk' t
      have hLower' : IsHermiteNormalFormFin (lowerRight t'.B) := by
        rw [hLowerEq]
        exact hLower
      have hzero' : ∀ i : Fin (m + 1), t'.B i.succ 0 = 0 := by
        simpa [t', hk'] using reduceTopRowLoop_below_zero k hk' t hzero
      intro i hi
      have hRowEq : t'.B i.succ = t.B i.succ := by
        simpa [t', hk'] using reduceTopRowLoop_lowerRow k hk' t i
      have hi' : i.1 < k ∨ i.1 = k := Nat.lt_succ_iff_lt_or_eq.mp hi
      rcases hi' with hi' | hEq
      · cases hcurr : firstNonzero? (fun s : Fin n => t'.B iCurr.succ s.succ) with
        | none =>
            rw [hloop, reduceTopRowStep, hcurr]
            simpa [t'] using ih hk' t hLower hzero i hi'
        | some p =>
            cases hrow : firstNonzero? (fun s : Fin n => t'.B i.succ s.succ) with
            | none =>
                have hrow' : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) = none := by
                  simpa [hRowEq] using hrow
                rw [hrow']
                simp
            | some q =>
                have hrow' : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) = some q := by
                  simpa [hRowEq] using hrow
                have hsrcZero : t'.B iCurr.succ q.succ = 0 := by
                  exact hnf_rowBelow_zero_at_pivot hLower'
                    (by simpa [iCurr] using hi') hrow
                have hprev :
                    t'.B 0 q.succ = t'.B 0 q.succ % t'.B i.succ q.succ := by
                  have hprev' := ih hk' t hLower hzero i hi'
                  simpa [t', hk', hrow', hRowEq] using hprev'
                have hden : t'.B i.succ q.succ = t.B i.succ q.succ := by
                  exact congrFun hRowEq q.succ
                rw [hrow', hloop]
                simpa [hden] using
                  reduceTopRowStep_preserves_reduced iCurr i t' hrow hprev hsrcZero
      · have : i = iCurr := Fin.ext hEq
        subst this
        have hRowEqCurr : t'.B iCurr.succ = t.B iCurr.succ := by
          simpa [t', hk'] using reduceTopRowLoop_lowerRow k hk' t iCurr
        cases hrow : firstNonzero? (fun s : Fin n => t'.B iCurr.succ s.succ) with
        | none =>
            have hrow' : firstNonzero? (fun s : Fin n => t.B iCurr.succ s.succ) = none := by
              simpa [hRowEqCurr] using hrow
            rw [hrow']
            simp
        | some q =>
            have hrow' : firstNonzero? (fun s : Fin n => t.B iCurr.succ s.succ) = some q := by
              simpa [hRowEqCurr] using hrow
            have hden : t'.B iCurr.succ q.succ = t.B iCurr.succ q.succ := by
              exact congrFun hRowEqCurr q.succ
            rw [hrow', hloop]
            simpa [hRowEqCurr] using reduceTopRowStep_current_reduced iCurr t' hrow


def hermiteNormalFormFin {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : FinHNFResult A := by
  induction n generalizing m with
  | zero =>
      refine
        { U := 1
          H := A
          left_mul := by simp
          unimodular := unimodular_one
          isHermite := IsHermiteNormalFormFin.emptyCols _ }
  | succ n ih =>
      cases m with
      | zero =>
          refine
            { U := 1
              H := A
              left_mul := by simp
              unimodular := unimodular_one
              isHermite := IsHermiteNormalFormFin.emptyRows _ }
      | succ m =>
          by_cases hcol : firstNonzero? (fun i : Fin (m + 1) => A i 0) = none
          · let tailRes := ih (m := m + 1) (tailCols A)
            refine
              { U := tailRes.U
                H := tailRes.U * A
                left_mul := by rfl
                unimodular := tailRes.unimodular
                isHermite := ?_ }
            refine IsHermiteNormalFormFin.zeroCol _ ?_ ?_
            · exact firstCol_zero_mul tailRes.U A (firstNonzero?_eq_none (fun i : Fin (m + 1) => A i 0) hcol)
            · simpa [tailCols_mul, tailRes.left_mul] using tailRes.isHermite
          · cases m with
            | zero =>
                have h00 : A 0 0 ≠ 0 := by
                  cases hfirst : firstNonzero? (fun i : Fin 1 => A i 0) with
                  | none =>
                      exact False.elim (hcol hfirst)
                  | some i =>
                      cases i using Fin.cases with
                      | zero =>
                          simpa using firstNonzero?_some_ne_zero (fun i : Fin 1 => A i 0) hfirst
                      | succ i =>
                          exact Fin.elim0 i
                let tNorm :=
                  LeftTransform.unitSmul A 0 (normUnit (A 0 0) : R) (normUnit (A 0 0)).isUnit
                have hNormEq : tNorm.B 0 0 = normalize (A 0 0) := by
                  simp [tNorm, LeftTransform.unitSmul, applyRowOperation, normalize_apply, mul_comm]
                refine
                  { U := tNorm.U
                    H := tNorm.B
                    left_mul := tNorm.left_mul
                    unimodular := tNorm.unimodular
                    isHermite := ?_ }
                refine IsHermiteNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_
                · rw [hNormEq]
                  exact mt normalize_eq_zero.mp h00
                · rw [hNormEq]
                  exact (normalize_idem (A 0 0)).symm
                · intro i
                  exact Fin.elim0 i
                · exact IsHermiteNormalFormFin.emptyRows _
                · intro i
                  exact Fin.elim0 i
            | succ m =>
                cases hfirst : firstNonzero? (fun i : Fin (m + 2) => A i 0) with
                | none =>
                    exact False.elim (hcol hfirst)
                | some i =>
                    let tSwap := LeftTransform.swap A i 0
                    let tNorm :=
                      tSwap.trans <|
                        LeftTransform.unitSmul tSwap.B 0 (normUnit (tSwap.B 0 0) : R)
                          (normUnit (tSwap.B 0 0)).isUnit
                    have hi0 : A i 0 ≠ 0 := firstNonzero?_some_ne_zero (fun i : Fin (m + 2) => A i 0) hfirst
                    have hNormEq : tNorm.B 0 0 = normalize (A i 0) := by
                      by_cases hi : i = 0
                      · subst hi
                        simp [tNorm, tSwap, LeftTransform.unitSmul, LeftTransform.swap,
                          LeftTransform.trans, applyRowOperation, normalize_apply, mul_comm]
                      · simp [tNorm, tSwap, LeftTransform.unitSmul, LeftTransform.swap,
                          LeftTransform.trans, applyRowOperation, normalize_apply, mul_comm,
                          show ¬ (0 : Fin (m + 2)) = i by simpa [eq_comm] using hi]
                    have hNormTopNonzero : tNorm.B 0 0 ≠ 0 := by
                      rw [hNormEq]
                      exact mt normalize_eq_zero.mp hi0
                    have hNormTopNormalized : tNorm.B 0 0 = normalize (tNorm.B 0 0) := by
                      rw [hNormEq]
                      exact (normalize_idem (A i 0)).symm
                    let tClear :=
                      clearFirstColumnLoop (A := A) (m := m) (n := n) (m + 1) le_rfl tNorm
                    let lowerRes := ih (m := m + 1) (lowerRight tClear.B)
                    let tLift :=
                      LeftTransform.diagLift tClear.B lowerRes.U lowerRes.unimodular
                    let tAfterLift := tClear.trans tLift
                    let tFinal :=
                      reduceTopRowLoop (A := A) (m := m) (n := n) (m + 1) le_rfl tAfterLift
                    have hClearTopNonzero : tClear.B 0 0 ≠ 0 := by
                      exact clearFirstColumnLoop_topLeft_ne_zero (m + 1) le_rfl tNorm hNormTopNonzero
                    have hClearTopNormalized : tClear.B 0 0 = normalize (tClear.B 0 0) := by
                      exact clearFirstColumnLoop_topLeft_normalized (m + 1) le_rfl tNorm hNormTopNormalized
                    have hClearBelow : ∀ r : Fin (m + 1), tClear.B r.succ 0 = 0 := by
                      intro r
                      exact clearFirstColumnLoop_prefix_zero (m + 1) le_rfl tNorm r r.is_lt
                    have hAfterLiftLower : lowerRight tAfterLift.B = lowerRes.H := by
                      simp [tAfterLift, tLift, LeftTransform.diagLift, LeftTransform.trans,
                        lowerRight_diagLiftMatrix_mul, lowerRes.left_mul]
                    have hAfterLiftTop : tAfterLift.B 0 0 = tClear.B 0 0 := by
                      simp [tAfterLift, tLift, LeftTransform.diagLift, LeftTransform.trans,
                        diagLiftMatrix_mul_topRow]
                    have hAfterLiftBelow : ∀ r : Fin (m + 1), tAfterLift.B r.succ 0 = 0 := by
                      intro r
                      simp [tAfterLift, tLift, LeftTransform.diagLift, LeftTransform.trans,
                        _root_.Matrix.mul_apply, diagLiftMatrix, hClearBelow, Fin.sum_univ_succ]
                    have hFinalTop : tFinal.B 0 0 = tAfterLift.B 0 0 := by
                      exact reduceTopRowLoop_topLeft (m + 1) le_rfl tAfterLift hAfterLiftBelow
                    have hFinalBelow : ∀ r : Fin (m + 1), tFinal.B r.succ 0 = 0 := by
                      exact reduceTopRowLoop_below_zero (m + 1) le_rfl tAfterLift hAfterLiftBelow
                    have hFinalLower : lowerRight tFinal.B = lowerRes.H := by
                      rw [reduceTopRowLoop_lowerRight (m + 1) le_rfl tAfterLift, hAfterLiftLower]
                    have hFinalReduced :
                        ∀ r : Fin (m + 1),
                          match firstNonzero? (fun s : Fin n => tFinal.B r.succ s.succ) with
                          | none => True
                          | some j =>
                              tFinal.B 0 j.succ = tFinal.B 0 j.succ % tFinal.B r.succ j.succ := by
                      intro r
                      have hLowerHNF : IsHermiteNormalFormFin (lowerRight tAfterLift.B) := by
                        simpa [hAfterLiftLower] using lowerRes.isHermite
                      have hRowEq : tFinal.B r.succ = tAfterLift.B r.succ := by
                        exact reduceTopRowLoop_lowerRow (m + 1) le_rfl tAfterLift r
                      simpa [hRowEq, reduceTopRowLoop_lowerRight (m + 1) le_rfl tAfterLift] using
                        reduceTopRowLoop_reduced_prefix (m + 1) le_rfl tAfterLift hLowerHNF
                          hAfterLiftBelow r r.is_lt
                    refine
                      { U := tFinal.U
                        H := tFinal.B
                        left_mul := tFinal.left_mul
                        unimodular := tFinal.unimodular
                        isHermite := ?_ }
                    refine IsHermiteNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_
                    · rw [hFinalTop, hAfterLiftTop]
                      exact hClearTopNonzero
                    · rw [hFinalTop, hAfterLiftTop]
                      exact hClearTopNormalized
                    · exact hFinalBelow
                    · simpa [hFinalLower] using lowerRes.isHermite
                    · exact hFinalReduced

end Internal


def HNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    LeftCertificate A :=
  { U := result.U
    result := result.H
    equation := result.left_mul }


noncomputable def hermiteNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : Option (HNFResult A) :=
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let Afin : _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) R :=
    _root_.Matrix.reindex em en A
  let result := Internal.hermiteNormalFormFin Afin
  some
    { U := _root_.Matrix.reindex em.symm em.symm result.U
      H := _root_.Matrix.reindex em.symm en.symm result.H
      left_mul := by
        simpa [Matrix.reindexLinearEquiv, Afin] using
          (Matrix.reindexLinearEquiv_mul R R em.symm em.symm en.symm result.U Afin).trans
            (by simpa [Matrix.reindexLinearEquiv, Afin] using congrArg (_root_.Matrix.reindex em.symm en.symm) result.left_mul)
      isHermite := by
        unfold IsHermiteNormalForm
        convert result.isHermite using 1
        ext i j
        simp [em, en] }


theorem hermiteNormalForm_exists {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : ∃ result, hermiteNormalForm A = some result := by
  unfold hermiteNormalForm
  simp


theorem hermiteNormalForm_unimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : HNFResult A}
    (hresult : hermiteNormalForm A = some result) :
    Unimodular result.U := by
  unfold hermiteNormalForm at hresult
  dsimp at hresult
  injection hresult with hEq
  subst hEq
  exact unimodular_reindex (Fintype.equivFin m).symm
    (Internal.hermiteNormalFormFin
      (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)).unimodular

end NormalForms.Matrix.Hermite
