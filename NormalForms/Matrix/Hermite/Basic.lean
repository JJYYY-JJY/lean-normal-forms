import NormalForms.Matrix.Certificates

/-!
# Hermite Normal Form API

Executable row-style Hermite normal forms over Euclidean domains.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates


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
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
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
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) : RowTransform A :=
  { B := A
    log := []
    rowLog := by simp
    unimodular := by simp
    replay_eq := by simp }


def RowTransform.singleton {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (op : RowOperation R m) (hop : UnimodularRowOperation op) :
    RowTransform A :=
  { B := applyRowOperation A op
    log := [.row op]
    rowLog := by simp [IsRowStep]
    unimodular := by
      simpa [List.Forall, UnimodularStep] using hop
    replay_eq := by rfl }


def RowTransform.trans {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (first : RowTransform A) (second : RowTransform first.B) :
    RowTransform A :=
  { B := second.B
    log := first.log ++ second.log
    rowLog := (listForall_append_iff first.log second.log).2 ⟨first.rowLog, second.rowLog⟩
    unimodular := (listForall_append_iff first.log second.log).2
      ⟨first.unimodular, second.unimodular⟩
    replay_eq := by
      rw [replayLog_append, first.replay_eq, second.replay_eq] }


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


theorem unimodularStep_mapStep {m m' n n' R : Type _} [CommRing R]
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


theorem mapLog_unimodular {m m' n n' R : Type _} [CommRing R]
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


def HNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    LeftCertificate A :=
  { U := result.U
    result := result.H
    equation := result.left_mul }


def hermiteNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : Option (HNFResult A) :=
  none

end NormalForms.Matrix.Hermite
