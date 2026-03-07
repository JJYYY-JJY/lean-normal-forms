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
  isHermite : IsHermiteNormalFormFin H


def pickRowLeftMatrix {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) :
    _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun r s =>
    if hr : r = 0 then
      (((normUnit (A i 0) : R) • (1 : _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R) i) s)
    else
      0


def pickRowResultMatrix {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) :
    _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R :=
  fun r c =>
    if r = 0 then
      normUnit (A i 0) * A i c
    else
      0


theorem pickRowLeftMatrix_topRow {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) :
    (pickRowLeftMatrix A i * A) 0 = fun c => normUnit (A i 0) * A i c := by
  ext c
  simpa [pickRowLeftMatrix, _root_.Matrix.mul_apply, Pi.smul_apply] using
    congrFun (basisRow_smul_vecMul A i (normUnit (A i 0) : R)) c


theorem pickRowLeftMatrix_lowerRow {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) (k : Fin m) :
    (pickRowLeftMatrix A i * A) k.succ = 0 := by
  ext c
  simp [pickRowLeftMatrix, _root_.Matrix.mul_apply]


theorem pickRowLeftMatrix_mul {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) :
    pickRowLeftMatrix A i * A = pickRowResultMatrix A i := by
  ext r c
  cases r using Fin.cases with
  | zero =>
      simpa [pickRowResultMatrix] using congrFun (pickRowLeftMatrix_topRow A i) c
  | succ k =>
      simpa [pickRowResultMatrix] using congrFun (pickRowLeftMatrix_lowerRow A i k) c


theorem pickRowResultMatrix_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) :
    pickRowResultMatrix A i 0 0 = normalize (A i 0) := by
  simpa [pickRowResultMatrix, mul_comm] using (normalize_apply (A i 0)).symm


theorem pickRowResultMatrix_topLeft_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) {i : Fin (m + 1)} (hi : A i 0 ≠ 0) :
    pickRowResultMatrix A i 0 0 ≠ 0 := by
  rw [pickRowResultMatrix_topLeft]
  exact mt normalize_eq_zero.mp hi


theorem pickRowResultMatrix_below_zero {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) :
    ∀ k : Fin m, pickRowResultMatrix A i k.succ 0 = 0 := by
  intro k
  simp [pickRowResultMatrix]


@[simp] theorem lowerRight_pickRowResultMatrix {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (m + 1)) :
    lowerRight (pickRowResultMatrix A i) = 0 := by
  ext j k
  simp [pickRowResultMatrix, lowerRight]


def hermiteNormalFormFin {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : FinHNFResult A := by
  induction n generalizing m with
  | zero =>
      refine
        { U := 1
          H := A
          left_mul := by simp
          isHermite := IsHermiteNormalFormFin.emptyCols _ }
  | succ n ih =>
      cases m with
      | zero =>
          refine
            { U := 1
              H := A
              left_mul := by simp
              isHermite := IsHermiteNormalFormFin.emptyRows _ }
      | succ m =>
          by_cases hcol : firstNonzero? (fun i : Fin (m + 1) => A i 0) = none
          · let tailRes := ih (m := m + 1) (tailCols A)
            refine
              { U := tailRes.U
                H := tailRes.U * A
                left_mul := by rfl
                isHermite := ?_ }
            refine IsHermiteNormalFormFin.zeroCol _ ?_ ?_
            · exact firstCol_zero_mul tailRes.U A (firstNonzero?_eq_none (fun i : Fin (m + 1) => A i 0) hcol)
            · simpa [tailCols_mul, tailRes.left_mul] using tailRes.isHermite
          · cases hfirst : firstNonzero? (fun i : Fin (m + 1) => A i 0) with
            | none =>
                exact False.elim (hcol hfirst)
            | some i =>
                have hi0 : A i 0 ≠ 0 := firstNonzero?_some_ne_zero (fun k : Fin (m + 1) => A k 0) hfirst
                refine
                  { U := pickRowLeftMatrix A i
                    H := pickRowResultMatrix A i
                    left_mul := pickRowLeftMatrix_mul A i
                    isHermite := ?_ }
                refine IsHermiteNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_
                · exact pickRowResultMatrix_topLeft_ne_zero A hi0
                · rw [pickRowResultMatrix_topLeft, normalize_idem]
                · intro k
                  exact pickRowResultMatrix_below_zero A i k
                · simpa using (zeroHermite (m := m) (n := n) :
                    IsHermiteNormalFormFin (0 : _root_.Matrix (Fin m) (Fin n) R))
                · intro k
                  have hrow : (fun j : Fin n => pickRowResultMatrix A i k.succ j.succ) = fun _ : Fin n => (0 : R) := by
                    funext j
                    simp [pickRowResultMatrix]
                  rw [hrow]
                  simp

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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : ∃ result, hermiteNormalForm A = some result := by
  unfold hermiteNormalForm
  simp

end NormalForms.Matrix.Hermite



