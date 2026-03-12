import NormalForms.Matrix.Hermite.Defs

/-!
# Hermite Transform Infrastructure

Row-only transform packaging and replay-transport lemmas for the Hermite algorithm.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates

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



end NormalForms.Matrix.Hermite
