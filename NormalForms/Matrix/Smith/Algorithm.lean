/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Euclidean.ComputableOps
public import NormalForms.Matrix.Smith.Defs
public import NormalForms.Matrix.Smith.Transform
public import NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Smith.Transform
import all NormalForms.Matrix.Hermite.Algorithm

/-!
# Smith Normal Form Algorithm

Internal same-size stabilization and the recursive executable Smith kernel.
-/

set_option linter.privateModule false

namespace NormalForms.Matrix.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

private theorem smithAlgorithmFinRangeNodup : ∀ n, (List.finRange n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.finRange_succ]
      apply List.Nodup.cons
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨i, _, hi⟩
        exact Fin.succ_ne_zero i hi
      · exact (smithAlgorithmFinRangeNodup n).map (Fin.succ_injective n)

@[implicit_reducible] private def smithAlgorithmFinFintype
    (n : Nat) : Fintype (Fin n) where
  elems := ⟨List.finRange n, smithAlgorithmFinRangeNodup n⟩
  complete := List.mem_finRange

attribute [local instance 20000] smithAlgorithmFinFintype

namespace Internal

/-! Constructive searches used by the compiled Smith kernel. -/

private def firstNonzeroWithOps? {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] :
    {n : Nat} -> (Fin n -> R) -> Option (Fin n)
  | 0, _ => none
  | _ + 1, row =>
      if ComputableEuclideanOps.isZeroB (row 0) = true then
        Option.map Fin.succ (firstNonzeroWithOps? fun j => row j.succ)
      else
        some 0


@[simp] private theorem firstNonzeroWithOps?_eq_firstNonzero?
    {R : Type _} [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R] [DecidableEq R] :
    {n : Nat} -> (row : Fin n -> R) ->
      firstNonzeroWithOps? row = firstNonzero? row
  | 0, _ => rfl
  | _ + 1, row => by
      by_cases h0 : row 0 = 0
      · simp [firstNonzeroWithOps?, firstNonzero?, h0,
          firstNonzeroWithOps?_eq_firstNonzero?]
      · have hzero :
            ComputableEuclideanOps.isZeroB (row 0) ≠ true :=
          fun h => h0 ((ComputableEuclideanOps.isZeroB_eq_true_iff _).1 h)
        simp [firstNonzeroWithOps?, firstNonzero?, h0, hzero]


private def firstUndivisibleWithOps? {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] :
    {n : Nat} -> R -> (Fin n -> R) -> Option (Fin n)
  | 0, _, _ => none
  | _ + 1, d, row =>
      if ComputableEuclideanOps.dvdB d (row 0) = true then
        Option.map Fin.succ (firstUndivisibleWithOps? d fun j => row j.succ)
      else
        some 0


private theorem firstUndivisibleWithOps?_eq_none
    {R : Type _} [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R] :
    {n : Nat} -> (d : R) -> (row : Fin n -> R) ->
      firstUndivisibleWithOps? d row = none ->
        ∀ i : Fin n, d ∣ row i
  | 0, _, _, _, i => Fin.elim0 i
  | _ + 1, d, row, hnone, i => by
      by_cases hdiv :
          ComputableEuclideanOps.dvdB d (row 0) = true
      · have htail :
            firstUndivisibleWithOps? d (fun j => row j.succ) = none := by
          simpa [firstUndivisibleWithOps?, hdiv] using hnone
        cases i using Fin.cases with
        | zero =>
            exact (ComputableEuclideanOps.dvdB_eq_true_iff _ _).1 hdiv
        | succ i =>
            exact firstUndivisibleWithOps?_eq_none
              d (fun j => row j.succ) htail i
      · have hsome :
            firstUndivisibleWithOps? d row =
              some (0 : Fin (_ + 1)) := by
          simp [firstUndivisibleWithOps?, hdiv]
        rw [hnone] at hsome
        cases hsome


private theorem firstUndivisibleWithOps?_some_not_dvd
    {R : Type _} [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R] :
    {n : Nat} -> (d : R) -> (row : Fin n -> R) -> {i : Fin n} ->
      firstUndivisibleWithOps? d row = some i ->
        ¬ d ∣ row i
  | 0, _, _, i, _ => Fin.elim0 i
  | _ + 1, d, row, i, hsome => by
      by_cases hdiv :
          ComputableEuclideanOps.dvdB d (row 0) = true
      · rw [firstUndivisibleWithOps?, hdiv] at hsome
        cases i using Fin.cases with
        | zero =>
            cases htail :
                firstUndivisibleWithOps? d (fun j => row j.succ) <;>
              simp [htail] at hsome
        | succ i =>
            cases htail :
                firstUndivisibleWithOps? d (fun j => row j.succ) with
            | none =>
                simp [htail] at hsome
            | some j =>
                have hji : j = i := by
                  simpa [htail] using hsome
                subst j
                exact firstUndivisibleWithOps?_some_not_dvd
                  d (fun j => row j.succ) htail
      · have hnot : ¬ d ∣ row 0 :=
          fun hdvd =>
            hdiv ((ComputableEuclideanOps.dvdB_eq_true_iff _ _).2 hdvd)
        have hzero :
            firstUndivisibleWithOps? d row =
              some (0 : Fin (_ + 1)) := by
          simp [firstUndivisibleWithOps?, hdiv]
        have hi : (0 : Fin (_ + 1)) = i := Option.some.inj <| hzero.symm.trans hsome
        subst i
        exact hnot


private theorem firstUndivisibleWithOps?_eq_firstUndivisible?
    {R : Type _} [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R] [DecidableEq R] :
    {n : Nat} -> (d : R) -> (row : Fin n -> R) ->
      firstUndivisibleWithOps? d row = firstUndivisible? d row
  | 0, _, _ => rfl
  | _ + 1, d, row => by
      by_cases hdiv : d ∣ row 0
      · have hbool : ComputableEuclideanOps.dvdB d (row 0) = true :=
          (ComputableEuclideanOps.dvdB_eq_true_iff _ _).2 hdiv
        have hmod : row 0 % d = 0 := EuclideanDomain.mod_eq_zero.mpr hdiv
        simp [firstUndivisibleWithOps?, firstUndivisible?, hbool, hmod,
          firstUndivisibleWithOps?_eq_firstUndivisible?]
      · have hbool : ComputableEuclideanOps.dvdB d (row 0) ≠ true :=
          fun h => hdiv ((ComputableEuclideanOps.dvdB_eq_true_iff _ _).1 h)
        have hmod : row 0 % d ≠ 0 :=
          fun h => hdiv (EuclideanDomain.mod_eq_zero.mp h)
        simp [firstUndivisibleWithOps?, firstUndivisible?, hbool, hmod]


private def firstUndivisibleLowerRightWithOps? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] :
    _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R ->
      R -> Option (Fin m × Fin n)
  | A, d =>
      let rec goRows : (k : Nat) -> k ≤ m -> Option (Fin m × Fin n)
        | 0, _ => none
        | k + 1, hk =>
            let hk' : k ≤ m :=
              Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            match goRows k hk' with
            | some p => some p
            | none =>
                let i : Fin m :=
                  ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                Option.map (fun j : Fin n => (i, j))
                  (firstUndivisibleWithOps? d fun j : Fin n => A i.succ j.succ)
      goRows m (Nat.le_refl _)


private theorem firstUndivisibleLowerRightWithOps?_eq
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (d : R) :
    firstUndivisibleLowerRightWithOps? A d =
      firstUndivisibleLowerRight? A d := by
  unfold firstUndivisibleLowerRightWithOps? firstUndivisibleLowerRight?
  have hgo :
      ∀ k (hk : k ≤ m),
        firstUndivisibleLowerRightWithOps?.goRows A d k hk =
          firstUndivisibleLowerRight?.goRows A d k hk := by
    intro k hk
    induction k with
    | zero =>
        rfl
    | succ k ih =>
        simp only [firstUndivisibleLowerRightWithOps?.goRows,
          firstUndivisibleLowerRight?.goRows]
        let hk' : k ≤ m :=
          Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
        rw [ih hk']
        cases hprev : firstUndivisibleLowerRight?.goRows A d k hk' with
        | some p =>
            simp
        | none =>
            simp [firstUndivisibleWithOps?_eq_firstUndivisible?]
  exact hgo m (Nat.le_refl m)


private theorem firstUndivisibleLowerRightWithOps?_eq_none
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (d : R)
    (hnone : firstUndivisibleLowerRightWithOps? A d = none) :
    ∀ i : Fin m, ∀ j : Fin n, d ∣ A i.succ j.succ := by
  unfold firstUndivisibleLowerRightWithOps? at hnone
  have hnone' :
      firstUndivisibleLowerRightWithOps?.goRows
          A d m (Nat.le_refl m) =
        none := by
    simpa [firstUndivisibleLowerRightWithOps?] using hnone
  let rowWitness :
      ∀ k (hk : k ≤ m),
        firstUndivisibleLowerRightWithOps?.goRows A d k hk = none ->
          ∀ i' : Fin m, i'.1 < k ->
            ∀ j' : Fin n, d ∣ A i'.succ j'.succ := by
    intro k
    induction k with
    | zero =>
        intro _ _ i' hi
        exact False.elim (Nat.not_lt_zero _ hi)
    | succ k ih =>
        intro hk hgo i' hi j'
        let hk' : k ≤ m :=
          Nat.le_of_lt
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hEq
        · have hgo' :
              firstUndivisibleLowerRightWithOps?.goRows
                  A d k hk' =
                none := by
            cases hrows :
                firstUndivisibleLowerRightWithOps?.goRows
                  A d k hk' with
            | none =>
                rfl
            | some p =>
                simp [firstUndivisibleLowerRightWithOps?.goRows,
                  hrows] at hgo
          exact ih hk' hgo' i' hi' j'
        · let i0 : Fin m :=
            ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
          have hi0 : i' = i0 := Fin.ext hEq
          subst i'
          cases hrows :
              firstUndivisibleLowerRightWithOps?.goRows
                A d k hk' with
          | some p =>
              simp [firstUndivisibleLowerRightWithOps?.goRows,
                hrows] at hgo
          | none =>
              cases hrow :
                  firstUndivisibleWithOps? d
                    (fun s : Fin n => A i0.succ s.succ) with
              | none =>
                  exact firstUndivisibleWithOps?_eq_none
                    d (fun s : Fin n => A i0.succ s.succ) hrow j'
              | some p =>
                  have hrowNone :
                      firstUndivisibleWithOps? d
                          (fun s : Fin n => A i0.succ s.succ) =
                        none := by
                    simpa [firstUndivisibleLowerRightWithOps?.goRows,
                      hrows, i0] using hgo
                  rw [hrow] at hrowNone
                  cases hrowNone
  intro i j
  exact rowWitness m (Nat.le_refl m) hnone' i i.is_lt j


private theorem firstUndivisibleLowerRightWithOps?_some_not_dvd
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (d : R) {p : Fin m × Fin n}
    (hsome : firstUndivisibleLowerRightWithOps? A d = some p) :
    ¬ d ∣ A p.1.succ p.2.succ := by
  unfold firstUndivisibleLowerRightWithOps? at hsome
  have hsome' :
      firstUndivisibleLowerRightWithOps?.goRows
          A d m (Nat.le_refl m) =
        some p := by
    simpa [firstUndivisibleLowerRightWithOps?] using hsome
  let rowWitness :
      ∀ k (hk : k ≤ m) {p : Fin m × Fin n},
        firstUndivisibleLowerRightWithOps?.goRows A d k hk = some p ->
          ¬ d ∣ A p.1.succ p.2.succ := by
    intro k
    induction k with
    | zero =>
        intro _ p h
        simp [firstUndivisibleLowerRightWithOps?.goRows] at h
    | succ k ih =>
        intro hk p h
        let hk' : k ≤ m :=
          Nat.le_of_lt
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
        cases hrows :
            firstUndivisibleLowerRightWithOps?.goRows
              A d k hk' with
        | some q =>
            have hqp : q = p := by
              simpa [firstUndivisibleLowerRightWithOps?.goRows,
                hrows] using h
            cases hqp
            exact ih hk' hrows
        | none =>
            let i : Fin m :=
              ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
            cases hrow :
                firstUndivisibleWithOps? d
                  (fun j : Fin n => A i.succ j.succ) with
            | none =>
                have hnone :
                    firstUndivisibleLowerRightWithOps?.goRows
                        A d (k + 1) hk =
                      none := by
                  simpa [firstUndivisibleLowerRightWithOps?.goRows,
                    hrows, hrow]
                rw [hnone] at h
                cases h
            | some j =>
                have hex :
                    ∃ a,
                      firstUndivisibleWithOps? d
                          (fun s : Fin n => A i.succ s.succ) =
                        some a ∧
                      (i, a) = p := by
                  simpa [firstUndivisibleLowerRightWithOps?.goRows,
                    hrows, i] using h
                rcases hex with ⟨a, ha, hpair⟩
                have haj : a = j :=
                  Option.some.inj <| ha.symm.trans hrow
                subst a
                cases hpair
                exact firstUndivisibleWithOps?_some_not_dvd
                  d (fun s : Fin n => A i.succ s.succ) hrow
  exact rowWitness m (Nat.le_refl m) hsome'


private def firstNonzeroEntryWithOps? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] :
    _root_.Matrix (Fin m) (Fin n) R -> Option (Fin m × Fin n)
  | A =>
      let rec goRows : (k : Nat) -> k ≤ m -> Option (Fin m × Fin n)
        | 0, _ => none
        | k + 1, hk =>
            let hk' : k ≤ m :=
              Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            match goRows k hk' with
            | some p => some p
            | none =>
                let i : Fin m :=
                  ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                match firstNonzeroWithOps? (fun j : Fin n => A i j) with
                | none => none
                | some j => some (i, j)
      goRows m (Nat.le_refl _)


@[simp] private theorem firstNonzeroEntryWithOps?_eq
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) :
    firstNonzeroEntryWithOps? A = firstNonzeroEntry? A := by
  unfold firstNonzeroEntryWithOps? firstNonzeroEntry?
  have hgo :
      ∀ k (hk : k ≤ m),
        firstNonzeroEntryWithOps?.goRows A k hk =
          firstNonzeroEntry?.goRows A k hk := by
    intro k hk
    induction k with
    | zero =>
        rfl
    | succ k ih =>
        simp only [firstNonzeroEntryWithOps?.goRows,
          firstNonzeroEntry?.goRows]
        let hk' : k ≤ m :=
          Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
        rw [ih hk']
        cases hprev : firstNonzeroEntry?.goRows A k hk' with
        | some p =>
            simp
        | none =>
            rw [firstNonzeroWithOps?_eq_firstNonzero?]
            simp only
            congr
  exact hgo m (Nat.le_refl m)


private theorem zeroSmith {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R] :
    IsSmithNormalFormFin (0 : _root_.Matrix (Fin m) (Fin n) R) := by
  induction m generalizing n with
  | zero =>
      exact IsSmithNormalFormFin.emptyRows _
  | succ m ih =>
      cases n with
      | zero =>
          exact IsSmithNormalFormFin.emptyCols _
      | succ n =>
          refine IsSmithNormalFormFin.zeroLead _ ?_ ?_ ?_ ?_
          · simp
          · intro j
            simp
          · intro i
            simp
          · ext i j
            simp [lowerRight]


end Internal

private theorem diagLiftMatrix_mul_zero_firstCol {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (hcol : ∀ i : Fin m, A i.succ 0 = 0) :
    ∀ i : Fin m, (diagLiftMatrix U * A) i.succ 0 = 0 := by
  intro i
  simp [diagLiftMatrix, _root_.Matrix.mul_apply,
    NormalForms.Matrix.Constructive.sum_univ_succ, hcol]


private theorem zero_topRow_mul_diagLiftMatrix {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (V : _root_.Matrix (Fin n) (Fin n) R)
    (hrow : ∀ j : Fin n, A 0 j.succ = 0) :
    ∀ j : Fin n, (A * diagLiftMatrix V) 0 j.succ = 0 := by
  intro j
  simp [diagLiftMatrix, _root_.Matrix.mul_apply,
    NormalForms.Matrix.Constructive.sum_univ_succ, hrow]


set_option linter.unusedDecidableInType false in
private theorem dvd_matrix_mul_of_right {l m n : Type _} {R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    {d : R} {A : _root_.Matrix l m R} {B : _root_.Matrix m n R}
    (hB : ∀ i j, d ∣ B i j) :
    ∀ i j, d ∣ (A * B) i j := by
  intro i j
  rw [_root_.Matrix.mul_apply]
  refine Finset.dvd_sum ?_
  intro k hk
  rcases hB k j with ⟨x, hx⟩
  refine ⟨A i k * x, ?_⟩
  calc
    A i k * B k j = A i k * (d * x) := by rw [hx]
    _ = d * (A i k * x) := by ring


set_option linter.unusedDecidableInType false in
private theorem dvd_matrix_mul_of_left {l m n : Type _} {R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    {d : R} {A : _root_.Matrix l m R} {B : _root_.Matrix m n R}
    (hA : ∀ i j, d ∣ A i j) :
    ∀ i j, d ∣ (A * B) i j := by
  intro i j
  rw [_root_.Matrix.mul_apply]
  refine Finset.dvd_sum ?_
  intro k hk
  rcases hA i k with ⟨x, hx⟩
  refine ⟨x * B k j, ?_⟩
  calc
    A i k * B k j = (d * x) * B k j := by rw [hx]
    _ = d * (x * B k j) := by ring

private theorem mod_ne_zero_of_not_dvd {R : Type _} [EuclideanDomain R]
    {a b : R} (_ha : a ≠ 0) (hnot : ¬ a ∣ b) :
    b % a ≠ 0 := by
  intro hmod
  exact hnot ((EuclideanDomain.mod_eq_zero).1 hmod)


private theorem gcd_dvd_mod {R : Type _} [EuclideanDomain R] [DecidableEq R]
    {a b : R} :
    EuclideanDomain.gcd a b ∣ b % a := by
  exact (EuclideanDomain.dvd_mod_iff (EuclideanDomain.gcd_dvd_left a b)).2
    (EuclideanDomain.gcd_dvd_right a b)


private theorem normalize_gcd_dvd_left {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {a b : R} :
    normalize (EuclideanDomain.gcd a b) ∣ a :=
  (normalize_dvd_iff).2 (EuclideanDomain.gcd_dvd_left a b)


private theorem normalize_gcd_dvd_right {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {a b : R} :
    normalize (EuclideanDomain.gcd a b) ∣ b :=
  (normalize_dvd_iff).2 (EuclideanDomain.gcd_dvd_right a b)


namespace Internal

structure PivotState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) where
  t : TwoSidedTransform A
  pivot_ne_zero : t.B 0 0 ≠ 0
  pivot_normalized : t.B 0 0 = normalize (t.B 0 0)


def initPivotFromEntry {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (p : Fin (m + 1) × Fin (n + 1)) (hp : A p.1 p.2 ≠ 0) :
    PivotState A := by
  let tRow := TwoSidedTransform.swapRows A p.1 0
  let tCol := tRow.trans (TwoSidedTransform.swapCols tRow.B p.2 0)
  let tNorm :=
    tCol.trans
      (TwoSidedTransform.unitSmulRow tCol.B 0 (ComputableEuclideanOps.normUnitUnit (tCol.B 0 0)))
  have htop : tCol.B 0 0 = A p.1 p.2 := by
    rcases p with ⟨i, j⟩
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [tCol, tRow, TwoSidedTransform.trans, TwoSidedTransform.swapRows,
        TwoSidedTransform.swapCols, applyRowOperation, applyColumnOperation, hi, hj, eq_comm]
  have hnormTop : tNorm.B 0 0 = normalize (A p.1 p.2) := by
    calc
      tNorm.B 0 0 = normalize (tCol.B 0 0) := by
        simp [tNorm, TwoSidedTransform.unitSmulRow, TwoSidedTransform.trans,
          applyRowOperation, normalize_apply, mul_comm]
      _ = normalize (A p.1 p.2) := by rw [htop]
  refine
    { t := tNorm
      pivot_ne_zero := ?_
      pivot_normalized := ?_ }
  · rw [hnormTop]
    exact mt normalize_eq_zero.mp hp
  · rw [hnormTop]
    exact
      (ComputableEuclideanOps.normalize_idem_constructive
        (A p.1 p.2)).symm


def initPivotState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (hA : A ≠ 0) :
    PivotState A := by
  cases hentry : firstNonzeroEntryWithOps? A with
  | none =>
      have hentry' : firstNonzeroEntry? A = none := by
        simpa using hentry
      exact False.elim (hA (firstNonzeroEntry?_eq_none A hentry'))
  | some p =>
      have hentry' : firstNonzeroEntry? A = some p := by
        simpa using hentry
      exact initPivotFromEntry A p (firstNonzeroEntry?_some_ne_zero A hentry')


structure LeadClearedState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) where
  t : TwoSidedTransform A
  pivot_ne_zero : t.B 0 0 ≠ 0
  pivot_normalized : t.B 0 0 = normalize (t.B 0 0)
  rowCleared : ∀ j : Fin n, t.B 0 j.succ = 0
  colCleared : ∀ i : Fin m, t.B i.succ 0 = 0


structure PivotDivisibleState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) where
  t : TwoSidedTransform A
  pivot_ne_zero : t.B 0 0 ≠ 0
  pivot_normalized : t.B 0 0 = normalize (t.B 0 0)
  rowCleared : ∀ j : Fin n, t.B 0 j.succ = 0
  colCleared : ∀ i : Fin m, t.B i.succ 0 = 0
  lowerRightDivisible : ∀ i : Fin m, ∀ j : Fin n, t.B 0 0 ∣ t.B i.succ j.succ


def PivotState.toLeadClearedState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A)
    (hrow : ∀ j : Fin n, s.t.B 0 j.succ = 0)
    (hcol : ∀ i : Fin m, s.t.B i.succ 0 = 0) :
    LeadClearedState A :=
  { t := s.t
    pivot_ne_zero := s.pivot_ne_zero
    pivot_normalized := s.pivot_normalized
    rowCleared := hrow
    colCleared := hcol }


def LeadClearedState.toPivotState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : LeadClearedState A) :
    PivotState A :=
  { t := s.t
    pivot_ne_zero := s.pivot_ne_zero
    pivot_normalized := s.pivot_normalized }


def LeadClearedState.toPivotDivisibleState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : LeadClearedState A)
    (hdiv : ∀ i : Fin m, ∀ j : Fin n, s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    PivotDivisibleState A :=
  { t := s.t
    pivot_ne_zero := s.pivot_ne_zero
    pivot_normalized := s.pivot_normalized
    rowCleared := s.rowCleared
    colCleared := s.colCleared
    lowerRightDivisible := hdiv }


def pivotIdeal {m n : Nat} {R : Type _} [EuclideanDomain R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) : Ideal R :=
  Ideal.span ({B 0 0} : Set R)


def PivotState.pivotIdeal {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) : Ideal R :=
  Internal.pivotIdeal s.t.B


def LeadClearedState.pivotIdeal {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : LeadClearedState A) : Ideal R :=
  Internal.pivotIdeal s.t.B


def PivotDivisibleState.pivotIdeal {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotDivisibleState A) : Ideal R :=
  Internal.pivotIdeal s.t.B

/-!
The recursive Smith kernel has not landed yet. This subsection therefore keeps
the same-size layer factored into reusable pieces:

- a pure algebra kernel on `a b : R`
- HNF-to-Smith bridge lemmas for exact top-left gcd formulas
- row/column `prepareLead...` raw steps on `TwoSidedTransform`
- same-size `prepareLead...` / `stabilizePivot` wrappers on `PivotState`
- a single-step `improvePivot` wrapper and a strict-descent theorem

The next phase can then add the outer recursion without refactoring these
proofs.
-/

def firstUndivisibleFirstCol? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) : Option (Fin m) :=
  firstUndivisibleWithOps? (B 0 0) (fun i : Fin m => B i.succ 0)


def firstUndivisibleFirstRow? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) : Option (Fin n) :=
  firstUndivisibleWithOps? (B 0 0) (fun j : Fin n => B 0 j.succ)


theorem firstUndivisibleFirstCol?_eq_none {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (hnone : firstUndivisibleFirstCol? B = none) :
    ∀ i : Fin m, B 0 0 ∣ B i.succ 0 := by
  exact firstUndivisibleWithOps?_eq_none
    (B 0 0) (fun i : Fin m => B i.succ 0) hnone


theorem firstUndivisibleFirstCol?_some_not_dvd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    {i : Fin m} (hsome : firstUndivisibleFirstCol? B = some i) :
    ¬ B 0 0 ∣ B i.succ 0 := by
  exact firstUndivisibleWithOps?_some_not_dvd
    (B 0 0) (fun j : Fin m => B j.succ 0) hsome


theorem firstUndivisibleFirstRow?_eq_none {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (hnone : firstUndivisibleFirstRow? B = none) :
    ∀ j : Fin n, B 0 0 ∣ B 0 j.succ := by
  exact firstUndivisibleWithOps?_eq_none
    (B 0 0) (fun j : Fin n => B 0 j.succ) hnone


theorem firstUndivisibleFirstRow?_some_not_dvd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    {j : Fin n} (hsome : firstUndivisibleFirstRow? B = some j) :
    ¬ B 0 0 ∣ B 0 j.succ := by
  exact firstUndivisibleWithOps?_some_not_dvd
    (B 0 0) (fun k : Fin n => B 0 k.succ) hsome


def prepareLeadColumnStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1)) : TwoSidedTransform A :=
  t.trans <|
    TwoSidedTransform.ofLeftTransform <|
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep i (LeftTransform.refl t.B)


def prepareLeadRowStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1)) : TwoSidedTransform A :=
  t.trans <|
    TwoSidedTransform.ofTransposeLeftTransform <|
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep j
        (LeftTransform.refl t.B.transpose)


theorem prepareLeadColumnStepData_topLeft_eq_xgcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1)) (hwit : t.B i.succ 0 ≠ 0) :
    (prepareLeadColumnStepData t i).B 0 0 =
      (ComputableEuclideanOps.xgcd
        (t.B 0 0) (t.B i.succ 0)).gcd := by
  change
    (NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep i
      (LeftTransform.refl t.B)).B 0 0 =
        (ComputableEuclideanOps.xgcd
          (t.B 0 0) (t.B i.succ 0)).gcd
  simpa [LeftTransform.refl] using
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_topLeft_eq_xgcd i
      (LeftTransform.refl t.B) hwit


theorem prepareLeadColumnStepData_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1))
    (htop : t.B 0 0 ≠ 0) (hwit : t.B i.succ 0 ≠ 0) :
    (prepareLeadColumnStepData t i).B 0 0 ≠ 0 := by
  rw [prepareLeadColumnStepData_topLeft_eq_xgcd t i hwit]
  intro hzero
  exact htop
    ((ComputableEuclideanOps.xgcd_gcd_eq_zero_iff
      (t.B 0 0) (t.B i.succ 0)).mp hzero).1


theorem prepareLeadColumnStepData_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1)) (hwit : t.B i.succ 0 ≠ 0) :
    (prepareLeadColumnStepData t i).B 0 0 =
      normalize ((prepareLeadColumnStepData t i).B 0 0) := by
  rw [prepareLeadColumnStepData_topLeft_eq_xgcd t i hwit]
  exact ComputableEuclideanOps.xgcd_gcd_normalized
    (t.B 0 0) (t.B i.succ 0)


theorem prepareLeadColumnStepData_preserves_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1))
    (hprefix : ∀ j : Fin (m + 1), j.1 < i.1 -> t.B j.succ 0 = 0) :
    ∀ j : Fin (m + 1), j.1 < i.1.succ -> (prepareLeadColumnStepData t i).B j.succ 0 = 0 := by
  intro j hj
  change
    (NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep i
      (LeftTransform.refl t.B)).B j.succ 0 = 0
  exact
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_prefix_zero i
      (LeftTransform.refl t.B) hprefix j hj


theorem prepareLeadRowStepData_topLeft_eq_xgcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1)) (hwit : t.B 0 j.succ ≠ 0) :
    (prepareLeadRowStepData t j).B 0 0 =
      (ComputableEuclideanOps.xgcd
        (t.B 0 0) (t.B 0 j.succ)).gcd := by
  change
    (NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep j
      (LeftTransform.refl t.B.transpose)).B.transpose 0 0 =
        (ComputableEuclideanOps.xgcd
          (t.B 0 0) (t.B 0 j.succ)).gcd
  simpa [LeftTransform.refl] using
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_topLeft_eq_xgcd j
      (LeftTransform.refl t.B.transpose) hwit


theorem prepareLeadRowStepData_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1))
    (htop : t.B 0 0 ≠ 0) (hwit : t.B 0 j.succ ≠ 0) :
    (prepareLeadRowStepData t j).B 0 0 ≠ 0 := by
  rw [prepareLeadRowStepData_topLeft_eq_xgcd t j hwit]
  intro hzero
  exact htop
    ((ComputableEuclideanOps.xgcd_gcd_eq_zero_iff
      (t.B 0 0) (t.B 0 j.succ)).mp hzero).1


theorem prepareLeadRowStepData_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1)) (hwit : t.B 0 j.succ ≠ 0) :
    (prepareLeadRowStepData t j).B 0 0 =
      normalize ((prepareLeadRowStepData t j).B 0 0) := by
  rw [prepareLeadRowStepData_topLeft_eq_xgcd t j hwit]
  exact ComputableEuclideanOps.xgcd_gcd_normalized
    (t.B 0 0) (t.B 0 j.succ)


theorem prepareLeadRowStepData_preserves_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1))
    (hprefix : ∀ c : Fin (n + 1), c.1 < j.1 -> t.B 0 c.succ = 0) :
    ∀ c : Fin (n + 1), c.1 < j.1.succ -> (prepareLeadRowStepData t j).B 0 c.succ = 0 := by
  have hprefixT :
      ∀ c : Fin (n + 1), c.1 < j.1 -> (LeftTransform.refl t.B.transpose).B c.succ 0 = 0 := by
    intro c hc
    change t.B 0 c.succ = 0
    exact hprefix c hc
  have hclear :=
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_prefix_zero j
      (LeftTransform.refl t.B.transpose) hprefixT
  intro c hc
  change
    (NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep j
      (LeftTransform.refl t.B.transpose)).B c.succ 0 = 0
  exact hclear c hc


theorem prepareLeadColumn_topLeft_eq_xgcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin (m + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (prepareLeadColumnStepData s.t i).B 0 0 =
      (ComputableEuclideanOps.xgcd
        (s.t.B 0 0) (s.t.B i.succ 0)).gcd := by
  have hwit : s.t.B i.succ 0 ≠ 0 := by
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  exact prepareLeadColumnStepData_topLeft_eq_xgcd s.t i hwit


theorem prepareLeadColumn_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin (m + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (prepareLeadColumnStepData s.t i).B 0 0 ≠ 0 := by
  have hwit : s.t.B i.succ 0 ≠ 0 := by
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  exact prepareLeadColumnStepData_pivot_ne_zero s.t i s.pivot_ne_zero hwit


theorem prepareLeadColumn_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin (m + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (prepareLeadColumnStepData s.t i).B 0 0 =
      normalize ((prepareLeadColumnStepData s.t i).B 0 0) := by
  have hwit : s.t.B i.succ 0 ≠ 0 := by
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  exact prepareLeadColumnStepData_pivot_normalized s.t i hwit


theorem prepareLeadColumn_strict_descent {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin (m + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (prepareLeadColumnStepData s.t i).B 0 0 ∣ s.t.B i.succ 0 % s.t.B 0 0 ∧
      s.t.B i.succ 0 % s.t.B 0 0 ≠ 0 ∧
      EuclideanDomain.r (s.t.B i.succ 0 % s.t.B 0 0) (s.t.B 0 0) := by
  have hmodNe : s.t.B i.succ 0 % s.t.B 0 0 ≠ 0 :=
    mod_ne_zero_of_not_dvd s.pivot_ne_zero hbad
  refine ⟨?_, hmodNe, EuclideanDomain.mod_lt _ s.pivot_ne_zero⟩
  rw [prepareLeadColumn_topLeft_eq_xgcd s i hbad,
    ComputableEuclideanOps.xgcd_gcd_eq_mathlib]
  exact (normalize_dvd_iff).2 (gcd_dvd_mod (a := s.t.B 0 0) (b := s.t.B i.succ 0))


def prepareLeadColumn {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin (m + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ 0) :
    PivotState A :=
  { t := prepareLeadColumnStepData s.t i
    pivot_ne_zero := prepareLeadColumn_pivot_ne_zero s i hbad
    pivot_normalized := prepareLeadColumn_pivot_normalized s i hbad }


theorem prepareLeadColumn_measure_lt {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin (m + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ 0) :
    ComputableEuclideanOps.measure ((prepareLeadColumn s i hbad).t.B 0 0) <
      ComputableEuclideanOps.measure (s.t.B 0 0) := by
  change
    ComputableEuclideanOps.measure ((prepareLeadColumnStepData s.t i).B 0 0) <
      ComputableEuclideanOps.measure (s.t.B 0 0)
  rw [prepareLeadColumn_topLeft_eq_xgcd s i hbad]
  have hlt := ComputableEuclideanOps.xgcd_measure_lt
    (a := s.t.B 0 0) (b := s.t.B i.succ 0) s.pivot_ne_zero hbad
  simpa [ComputableEuclideanOps.normalize_eq_mathlib, ← s.pivot_normalized] using hlt


theorem prepareLeadRow_topLeft_eq_xgcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (s : PivotState A) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (prepareLeadRowStepData s.t j).B 0 0 =
      (ComputableEuclideanOps.xgcd
        (s.t.B 0 0) (s.t.B 0 j.succ)).gcd := by
  have hwit : s.t.B 0 j.succ ≠ 0 := by
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  exact prepareLeadRowStepData_topLeft_eq_xgcd s.t j hwit


theorem prepareLeadRow_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (s : PivotState A) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (prepareLeadRowStepData s.t j).B 0 0 ≠ 0 := by
  have hwit : s.t.B 0 j.succ ≠ 0 := by
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  exact prepareLeadRowStepData_pivot_ne_zero s.t j s.pivot_ne_zero hwit


theorem prepareLeadRow_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (s : PivotState A) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (prepareLeadRowStepData s.t j).B 0 0 =
      normalize ((prepareLeadRowStepData s.t j).B 0 0) := by
  have hwit : s.t.B 0 j.succ ≠ 0 := by
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  exact prepareLeadRowStepData_pivot_normalized s.t j hwit


theorem prepareLeadRow_strict_descent {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (s : PivotState A) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (prepareLeadRowStepData s.t j).B 0 0 ∣ s.t.B 0 j.succ % s.t.B 0 0 ∧
      s.t.B 0 j.succ % s.t.B 0 0 ≠ 0 ∧
      EuclideanDomain.r (s.t.B 0 j.succ % s.t.B 0 0) (s.t.B 0 0) := by
  have hmodNe : s.t.B 0 j.succ % s.t.B 0 0 ≠ 0 :=
    mod_ne_zero_of_not_dvd s.pivot_ne_zero hbad
  refine ⟨?_, hmodNe, EuclideanDomain.mod_lt _ s.pivot_ne_zero⟩
  rw [prepareLeadRow_topLeft_eq_xgcd s j hbad,
    ComputableEuclideanOps.xgcd_gcd_eq_mathlib]
  exact (normalize_dvd_iff).2 (gcd_dvd_mod (a := s.t.B 0 0) (b := s.t.B 0 j.succ))


def prepareLeadRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (s : PivotState A) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    PivotState A :=
  { t := prepareLeadRowStepData s.t j
    pivot_ne_zero := prepareLeadRow_pivot_ne_zero s j hbad
    pivot_normalized := prepareLeadRow_pivot_normalized s j hbad }


theorem prepareLeadRow_measure_lt {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (s : PivotState A) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    ComputableEuclideanOps.measure ((prepareLeadRow s j hbad).t.B 0 0) <
      ComputableEuclideanOps.measure (s.t.B 0 0) := by
  change
    ComputableEuclideanOps.measure ((prepareLeadRowStepData s.t j).B 0 0) <
      ComputableEuclideanOps.measure (s.t.B 0 0)
  rw [prepareLeadRow_topLeft_eq_xgcd s j hbad]
  have hlt := ComputableEuclideanOps.xgcd_measure_lt
    (a := s.t.B 0 0) (b := s.t.B 0 j.succ) s.pivot_ne_zero hbad
  simpa [ComputableEuclideanOps.normalize_eq_mathlib, ← s.pivot_normalized] using hlt


def injectLowerRightWitnessToFirstColData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (_i : Fin (m + 1)) (j : Fin (n + 1)) : TwoSidedTransform A :=
  s.t.trans
    (TwoSidedTransform.addCols s.t.B j.succ 0 (1 : R) (by simp))


theorem injectLowerRightWitnessToFirstCol_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (injectLowerRightWitnessToFirstColData s i j).B 0 0 = s.t.B 0 0 := by
  simp [injectLowerRightWitnessToFirstColData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, s.rowCleared j]


theorem injectLowerRightWitnessToFirstCol_target {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (injectLowerRightWitnessToFirstColData s i j).B i.succ 0 = s.t.B i.succ j.succ := by
  simp [injectLowerRightWitnessToFirstColData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, s.colCleared i]


def improvePivotStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1)) : TwoSidedTransform A :=
  prepareLeadColumnStepData (injectLowerRightWitnessToFirstColData s i j) i


theorem improvePivot_topLeft_eq_xgcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 =
      (ComputableEuclideanOps.xgcd
        (s.t.B 0 0) (s.t.B i.succ j.succ)).gcd := by
  have hwit : (injectLowerRightWitnessToFirstColData s i j).B i.succ 0 ≠ 0 := by
    rw [injectLowerRightWitnessToFirstCol_target s i j]
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  calc
    (improvePivotStepData s i j).B 0 0
        = (ComputableEuclideanOps.xgcd
              ((injectLowerRightWitnessToFirstColData s i j).B 0 0)
              ((injectLowerRightWitnessToFirstColData s i j).B i.succ 0)).gcd := by
              exact prepareLeadColumnStepData_topLeft_eq_xgcd
                (injectLowerRightWitnessToFirstColData s i j) i hwit
    _ = (ComputableEuclideanOps.xgcd
          (s.t.B 0 0) (s.t.B i.succ j.succ)).gcd := by
          rw [injectLowerRightWitnessToFirstCol_topLeft s i j,
            injectLowerRightWitnessToFirstCol_target s i j]


theorem improvePivot_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 ≠ 0 := by
  rw [improvePivot_topLeft_eq_xgcd s i j hbad]
  intro hzero
  exact s.pivot_ne_zero
    ((ComputableEuclideanOps.xgcd_gcd_eq_zero_iff
      (s.t.B 0 0) (s.t.B i.succ j.succ)).mp hzero).1


theorem improvePivot_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 =
      normalize ((improvePivotStepData s i j).B 0 0) := by
  rw [improvePivot_topLeft_eq_xgcd s i j hbad]
  exact ComputableEuclideanOps.xgcd_gcd_normalized
    (s.t.B 0 0) (s.t.B i.succ j.succ)


theorem improvePivot_strict_descent {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 ∣ s.t.B i.succ j.succ % s.t.B 0 0 ∧
      s.t.B i.succ j.succ % s.t.B 0 0 ≠ 0 ∧
      EuclideanDomain.r (s.t.B i.succ j.succ % s.t.B 0 0) (s.t.B 0 0) := by
  have hmodNe : s.t.B i.succ j.succ % s.t.B 0 0 ≠ 0 :=
    mod_ne_zero_of_not_dvd s.pivot_ne_zero hbad
  refine ⟨?_, hmodNe, EuclideanDomain.mod_lt _ s.pivot_ne_zero⟩
  rw [improvePivot_topLeft_eq_xgcd s i j hbad,
    ComputableEuclideanOps.xgcd_gcd_eq_mathlib]
  exact (normalize_dvd_iff).2 (gcd_dvd_mod (a := s.t.B 0 0) (b := s.t.B i.succ j.succ))


def improvePivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    PivotState A :=
  { t := improvePivotStepData s i j
    pivot_ne_zero := improvePivot_pivot_ne_zero s i j hbad
    pivot_normalized := improvePivot_pivot_normalized s i j hbad }


theorem improvePivot_measure_lt {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    ComputableEuclideanOps.measure ((improvePivot s i j hbad).t.B 0 0) <
      ComputableEuclideanOps.measure (s.t.B 0 0) := by
  change
    ComputableEuclideanOps.measure ((improvePivotStepData s i j).B 0 0) <
      ComputableEuclideanOps.measure (s.t.B 0 0)
  rw [improvePivot_topLeft_eq_xgcd s i j hbad]
  have hlt := ComputableEuclideanOps.xgcd_measure_lt
    (a := s.t.B 0 0) (b := s.t.B i.succ j.succ) s.pivot_ne_zero hbad
  simpa [ComputableEuclideanOps.normalize_eq_mathlib, ← s.pivot_normalized] using hlt


private def clearFirstColumnCoeff {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin m) : R :=
  -(ComputableEuclideanOps.quot (B i.succ 0) (B 0 0))


private def clearFirstRowCoeff {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (j : Fin n) : R :=
  -(ComputableEuclideanOps.quot (B 0 j.succ) (B 0 0))


private def clearFirstColumnByPivotStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin m) : TwoSidedTransform A :=
  t.trans
    (TwoSidedTransform.addRows t.B 0 i.succ (clearFirstColumnCoeff t.B i)
      (by simp [eq_comm]))


private def clearFirstRowByPivotStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j : Fin n) : TwoSidedTransform A :=
  t.trans
    (TwoSidedTransform.addCols t.B 0 j.succ (clearFirstRowCoeff t.B j)
      (by simp [eq_comm]))


private def clearFirstColumnByPivotTransform {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) : TwoSidedTransform A :=
  clearFirstColumnByPivotStepData s.t i


private def clearFirstRowByPivotTransform {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) : TwoSidedTransform A :=
  clearFirstRowByPivotStepData s.t j


@[simp] theorem clearFirstColumnByPivotTransform_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) :
    (clearFirstColumnByPivotTransform s i).B 0 0 = s.t.B 0 0 := by
  have hne : (0 : Fin (m + 1)) ≠ i.succ := by
    simp [eq_comm]
  change (clearFirstColumnByPivotStepData s.t i).B 0 0 = s.t.B 0 0
  simp [clearFirstColumnByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addRows,
    applyRowOperation, hne]


@[simp] theorem clearFirstRowByPivotTransform_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) :
    (clearFirstRowByPivotTransform s j).B 0 0 = s.t.B 0 0 := by
  have hne : (0 : Fin (n + 1)) ≠ j.succ := by
    simp [eq_comm]
  change (clearFirstRowByPivotStepData s.t j).B 0 0 = s.t.B 0 0
  simp [clearFirstRowByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, hne]


def clearFirstColumnByPivotStep {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m)
    (_hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
    PivotState A :=
  let t := clearFirstColumnByPivotTransform s i
  { t := t
    pivot_ne_zero := by
      rw [clearFirstColumnByPivotTransform_topLeft]
      exact s.pivot_ne_zero
    pivot_normalized := by
      rw [clearFirstColumnByPivotTransform_topLeft]
      exact s.pivot_normalized }

def clearFirstRowByPivotStep {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n)
    (_hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    PivotState A :=
  let t := clearFirstRowByPivotTransform s j
  { t := t
    pivot_ne_zero := by
      rw [clearFirstRowByPivotTransform_topLeft]
      exact s.pivot_ne_zero
    pivot_normalized := by
      rw [clearFirstRowByPivotTransform_topLeft]
      exact s.pivot_normalized }


@[simp] theorem clearFirstColumnByPivotStep_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (clearFirstColumnByPivotStep s i hdiv).t.B 0 0 = s.t.B 0 0 := by
  change (clearFirstColumnByPivotTransform s i).B 0 0 = s.t.B 0 0
  simp


theorem clearFirstColumnByPivotStep_topRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) (j : Fin (n + 1)) :
    (clearFirstColumnByPivotStep s i hdiv).t.B 0 j = s.t.B 0 j := by
  have hne : (0 : Fin (m + 1)) ≠ i.succ := by
    simp [eq_comm]
  change (clearFirstColumnByPivotStepData s.t i).B 0 j = s.t.B 0 j
  simp [clearFirstColumnByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addRows,
    applyRowOperation, hne]


theorem clearFirstColumnByPivotStep_otherRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i r : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) (hri : r ≠ i) :
    (clearFirstColumnByPivotStep s i hdiv).t.B r.succ = s.t.B r.succ := by
  ext j
  have hne : r.succ ≠ i.succ := by
    intro h
    apply hri
    apply Fin.ext
    exact Nat.succ.inj <| by simpa using congrArg Fin.val h
  change (clearFirstColumnByPivotStepData s.t i).B r.succ j = s.t.B r.succ j
  simp [clearFirstColumnByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addRows,
    applyRowOperation, hne]


theorem clearFirstColumnByPivotStep_target_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (clearFirstColumnByPivotStep s i hdiv).t.B i.succ 0 = 0 := by
  have hmul :
      ComputableEuclideanOps.quot (s.t.B i.succ 0) (s.t.B 0 0) *
          s.t.B 0 0 =
        s.t.B i.succ 0 := by
    rw [mul_comm]
    exact ComputableEuclideanOps.mul_quot_cancel_of_dvd
      s.pivot_ne_zero hdiv
  calc
    (clearFirstColumnByPivotStep s i hdiv).t.B i.succ 0
        = s.t.B i.succ 0 +
            (-ComputableEuclideanOps.quot
              (s.t.B i.succ 0) (s.t.B 0 0)) * s.t.B 0 0 := by
            change (clearFirstColumnByPivotStepData s.t i).B i.succ 0 =
              s.t.B i.succ 0 +
                (-ComputableEuclideanOps.quot
                  (s.t.B i.succ 0) (s.t.B 0 0)) * s.t.B 0 0
            simp [clearFirstColumnByPivotStepData, TwoSidedTransform.trans,
              TwoSidedTransform.addRows, clearFirstColumnCoeff, applyRowOperation]
    _ = s.t.B i.succ 0 -
          ComputableEuclideanOps.quot
            (s.t.B i.succ 0) (s.t.B 0 0) * s.t.B 0 0 := by
          ring
    _ = 0 := by rw [hmul]; ring


theorem clearFirstColumnByPivotStep_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0)
    (hprefix : ∀ j : Fin m, j.1 < i.1 -> s.t.B j.succ 0 = 0) :
    ∀ j : Fin m, j.1 < i.1.succ -> (clearFirstColumnByPivotStep s i hdiv).t.B j.succ 0 = 0 := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hEq
  · rw [show (clearFirstColumnByPivotStep s i hdiv).t.B j.succ 0 = s.t.B j.succ 0 by
      have hji : j ≠ i := by
        intro h
        subst h
        exact Nat.lt_irrefl _ hj'
      exact congrFun (clearFirstColumnByPivotStep_otherRow s i j hdiv hji) 0]
    exact hprefix j hj'
  · have hji : j = i := Fin.ext hEq
    subst j
    exact clearFirstColumnByPivotStep_target_zero s i hdiv


@[simp] theorem clearFirstRowByPivotStep_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (clearFirstRowByPivotStep s j hdiv).t.B 0 0 = s.t.B 0 0 := by
  change (clearFirstRowByPivotTransform s j).B 0 0 = s.t.B 0 0
  simp


theorem clearFirstRowByPivotStep_firstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) (i : Fin (m + 1)) :
    (clearFirstRowByPivotStep s j hdiv).t.B i 0 = s.t.B i 0 := by
  have hne : (0 : Fin (n + 1)) ≠ j.succ := by
    simp [eq_comm]
  change (clearFirstRowByPivotStepData s.t j).B i 0 = s.t.B i 0
  simp [clearFirstRowByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, hne]


theorem clearFirstRowByPivotStep_otherCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j c : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) (hcj : c ≠ j)
    (i : Fin (m + 1)) :
    (clearFirstRowByPivotStep s j hdiv).t.B i c.succ = s.t.B i c.succ := by
  have hne : c.succ ≠ j.succ := by
    intro h
    apply hcj
    apply Fin.ext
    exact Nat.succ.inj <| by simpa using congrArg Fin.val h
  change (clearFirstRowByPivotStepData s.t j).B i c.succ = s.t.B i c.succ
  simp [clearFirstRowByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, hne]


theorem clearFirstRowByPivotStep_target_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (clearFirstRowByPivotStep s j hdiv).t.B 0 j.succ = 0 := by
  have hmul :
      s.t.B 0 0 *
          ComputableEuclideanOps.quot (s.t.B 0 j.succ) (s.t.B 0 0) =
        s.t.B 0 j.succ :=
    ComputableEuclideanOps.mul_quot_cancel_of_dvd
      s.pivot_ne_zero hdiv
  calc
    (clearFirstRowByPivotStep s j hdiv).t.B 0 j.succ
        = s.t.B 0 j.succ +
            (-ComputableEuclideanOps.quot
              (s.t.B 0 j.succ) (s.t.B 0 0)) * s.t.B 0 0 := by
            change (clearFirstRowByPivotStepData s.t j).B 0 j.succ =
              s.t.B 0 j.succ +
                (-ComputableEuclideanOps.quot
                  (s.t.B 0 j.succ) (s.t.B 0 0)) * s.t.B 0 0
            simp [clearFirstRowByPivotStepData, TwoSidedTransform.trans,
              TwoSidedTransform.addCols, clearFirstRowCoeff, applyColumnOperation]
    _ = s.t.B 0 j.succ -
          ComputableEuclideanOps.quot
            (s.t.B 0 j.succ) (s.t.B 0 0) * s.t.B 0 0 := by
          ring
    _ = 0 := by
          rw [show ComputableEuclideanOps.quot
              (s.t.B 0 j.succ) (s.t.B 0 0) * s.t.B 0 0 =
                s.t.B 0 j.succ by
            simpa [mul_comm] using hmul]
          ring


theorem clearFirstRowByPivotStep_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ)
    (hprefix : ∀ c : Fin n, c.1 < j.1 -> s.t.B 0 c.succ = 0) :
    ∀ c : Fin n, c.1 < j.1.succ -> (clearFirstRowByPivotStep s j hdiv).t.B 0 c.succ = 0 := by
  intro c hc
  rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | hEq
  · rw [show (clearFirstRowByPivotStep s j hdiv).t.B 0 c.succ = s.t.B 0 c.succ by
      have hcj : c ≠ j := by
        intro h
        subst h
        exact Nat.lt_irrefl _ hc'
      exact clearFirstRowByPivotStep_otherCol s j c hdiv hcj 0]
    exact hprefix c hc'
  · have hcj : c = j := Fin.ext hEq
    subst c
    exact clearFirstRowByPivotStep_target_zero s j hdiv


theorem clearFirstColumnByPivotStepData_eq {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
    clearFirstColumnByPivotStepData s.t i = (clearFirstColumnByPivotStep s i hdiv).t :=
  rfl


theorem clearFirstRowByPivotStepData_eq {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    clearFirstRowByPivotStepData s.t j = (clearFirstRowByPivotStep s j hdiv).t :=
  rfl


private theorem clearFirstColumnByPivotStepData_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin m)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (_hdiv : t.B 0 0 ∣ t.B i.succ 0) :
    (clearFirstColumnByPivotStepData t i).B 0 0 = t.B 0 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstColumnByPivotTransform s i).B 0 0 = s.t.B 0 0
  exact clearFirstColumnByPivotTransform_topLeft s i


private theorem clearFirstColumnByPivotStepData_topRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin m)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B i.succ 0)
    (j : Fin (n + 1)) :
    (clearFirstColumnByPivotStepData t i).B 0 j = t.B 0 j := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstColumnByPivotStepData s.t i).B 0 j = s.t.B 0 j
  rw [clearFirstColumnByPivotStepData_eq s i hdiv]
  exact clearFirstColumnByPivotStep_topRow s i hdiv j


private theorem clearFirstColumnByPivotStepData_otherRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i r : Fin m)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B i.succ 0)
    (hri : r ≠ i) :
    (clearFirstColumnByPivotStepData t i).B r.succ = t.B r.succ := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstColumnByPivotStepData s.t i).B r.succ = s.t.B r.succ
  rw [clearFirstColumnByPivotStepData_eq s i hdiv]
  exact clearFirstColumnByPivotStep_otherRow s i r hdiv hri


private theorem clearFirstColumnByPivotStepData_target_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin m)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B i.succ 0) :
    (clearFirstColumnByPivotStepData t i).B i.succ 0 = 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstColumnByPivotStepData s.t i).B i.succ 0 = 0
  rw [clearFirstColumnByPivotStepData_eq s i hdiv]
  exact clearFirstColumnByPivotStep_target_zero s i hdiv


private theorem clearFirstColumnByPivotStepData_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin m)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B i.succ 0)
    (hprefix : ∀ j : Fin m, j.1 < i.1 -> t.B j.succ 0 = 0) :
    ∀ j : Fin m, j.1 < i.1.succ -> (clearFirstColumnByPivotStepData t i).B j.succ 0 = 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change
    ∀ j : Fin m, j.1 < i.1.succ ->
      (clearFirstColumnByPivotStepData s.t i).B j.succ 0 = 0
  rw [clearFirstColumnByPivotStepData_eq s i hdiv]
  exact clearFirstColumnByPivotStep_prefix_zero s i hdiv hprefix


private theorem clearFirstRowByPivotStepData_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j : Fin n)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (_hdiv : t.B 0 0 ∣ t.B 0 j.succ) :
    (clearFirstRowByPivotStepData t j).B 0 0 = t.B 0 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstRowByPivotTransform s j).B 0 0 = s.t.B 0 0
  exact clearFirstRowByPivotTransform_topLeft s j


private theorem clearFirstRowByPivotStepData_firstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j : Fin n)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B 0 j.succ)
    (i : Fin (m + 1)) :
    (clearFirstRowByPivotStepData t j).B i 0 = t.B i 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstRowByPivotStepData s.t j).B i 0 = s.t.B i 0
  rw [clearFirstRowByPivotStepData_eq s j hdiv]
  exact clearFirstRowByPivotStep_firstCol s j hdiv i


private theorem clearFirstRowByPivotStepData_otherCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j c : Fin n)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B 0 j.succ)
    (hcj : c ≠ j)
    (i : Fin (m + 1)) :
    (clearFirstRowByPivotStepData t j).B i c.succ = t.B i c.succ := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstRowByPivotStepData s.t j).B i c.succ = s.t.B i c.succ
  rw [clearFirstRowByPivotStepData_eq s j hdiv]
  exact clearFirstRowByPivotStep_otherCol s j c hdiv hcj i


private theorem clearFirstRowByPivotStepData_target_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j : Fin n)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B 0 j.succ) :
    (clearFirstRowByPivotStepData t j).B 0 j.succ = 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstRowByPivotStepData s.t j).B 0 j.succ = 0
  rw [clearFirstRowByPivotStepData_eq s j hdiv]
  exact clearFirstRowByPivotStep_target_zero s j hdiv


private theorem clearFirstRowByPivotStepData_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j : Fin n)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B 0 j.succ)
    (hprefix : ∀ c : Fin n, c.1 < j.1 -> t.B 0 c.succ = 0) :
    ∀ c : Fin n, c.1 < j.1.succ -> (clearFirstRowByPivotStepData t j).B 0 c.succ = 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change
    ∀ c : Fin n, c.1 < j.1.succ ->
      (clearFirstRowByPivotStepData s.t j).B 0 c.succ = 0
  rw [clearFirstRowByPivotStepData_eq s j hdiv]
  exact clearFirstRowByPivotStep_prefix_zero s j hdiv hprefix


def clearFirstColumnByPivotLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ m -> TwoSidedTransform A -> TwoSidedTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnByPivotLoop k hk' t
      let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      clearFirstColumnByPivotStepData t' i


def clearFirstRowByPivotLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ n -> TwoSidedTransform A -> TwoSidedTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let hk' : k ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstRowByPivotLoop k hk' t
      let j : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      clearFirstRowByPivotStepData t' j


private theorem clearFirstColumnByPivotLoop_topLeft_colDivisible {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ i : Fin m, t.B 0 0 ∣ t.B i.succ 0) :
    (clearFirstColumnByPivotLoop k hk t).B 0 0 = t.B 0 0 ∧
      ∀ i : Fin m, (clearFirstColumnByPivotLoop k hk t).B 0 0 ∣
        (clearFirstColumnByPivotLoop k hk t).B i.succ 0 := by
  induction k generalizing t with
  | zero =>
      refine ⟨rfl, ?_⟩
      simpa [clearFirstColumnByPivotLoop] using hdiv
  | succ k ih =>
      let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnByPivotLoop k hk' t
      let iCurr : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have ih' := ih hk' t htop hnorm hdiv
      have htopEq' : t'.B 0 0 = t.B 0 0 := by
        simpa [t', hk'] using ih'.1
      have htop' : t'.B 0 0 ≠ 0 := by
        rw [htopEq']
        exact htop
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        calc
          t'.B 0 0 = t.B 0 0 := htopEq'
          _ = normalize (t.B 0 0) := hnorm
          _ = normalize (t'.B 0 0) := by rw [htopEq']
      have hdiv' : ∀ i : Fin m, t'.B 0 0 ∣ t'.B i.succ 0 := by
        intro i
        simpa [t', hk'] using ih'.2 i
      refine ⟨?_, ?_⟩
      · calc
          (clearFirstColumnByPivotLoop (k + 1) hk t).B 0 0
              = (clearFirstColumnByPivotStepData t' iCurr).B 0 0 := by
                  rfl
          _ = t'.B 0 0 := by
                exact clearFirstColumnByPivotStepData_topLeft t' iCurr htop' hnorm' (hdiv' iCurr)
          _ = t.B 0 0 := htopEq'
      · intro i
        by_cases hi : i = iCurr
        · subst hi
          rw [show (clearFirstColumnByPivotLoop (k + 1) hk t).B iCurr.succ 0 =
              (clearFirstColumnByPivotStepData t' iCurr).B iCurr.succ 0 by
                rfl]
          rw [clearFirstColumnByPivotStepData_target_zero t' iCurr htop' hnorm' (hdiv' iCurr)]
          exact dvd_zero _
        · calc
            (clearFirstColumnByPivotLoop (k + 1) hk t).B 0 0
                = (clearFirstColumnByPivotStepData t' iCurr).B 0 0 := by
                    rfl
            _ = t'.B 0 0 := by
                  exact clearFirstColumnByPivotStepData_topLeft t' iCurr htop' hnorm' (hdiv' iCurr)
            _ ∣ t'.B i.succ 0 := hdiv' i
            _ = (clearFirstColumnByPivotStepData t' iCurr).B i.succ 0 := by
                  symm
                  exact congrFun
                    (clearFirstColumnByPivotStepData_otherRow t' iCurr i htop' hnorm'
                      (hdiv' iCurr) hi) 0
            _ = (clearFirstColumnByPivotLoop (k + 1) hk t).B i.succ 0 := by
                  rfl


private theorem clearFirstRowByPivotLoop_topLeft_rowDivisible {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ n) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ j : Fin n, t.B 0 0 ∣ t.B 0 j.succ) :
    (clearFirstRowByPivotLoop k hk t).B 0 0 = t.B 0 0 ∧
      ∀ j : Fin n, (clearFirstRowByPivotLoop k hk t).B 0 0 ∣
        (clearFirstRowByPivotLoop k hk t).B 0 j.succ := by
  induction k generalizing t with
  | zero =>
      refine ⟨rfl, ?_⟩
      simpa [clearFirstRowByPivotLoop] using hdiv
  | succ k ih =>
      let hk' : k ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstRowByPivotLoop k hk' t
      let jCurr : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have ih' := ih hk' t htop hnorm hdiv
      have htopEq' : t'.B 0 0 = t.B 0 0 := by
        simpa [t', hk'] using ih'.1
      have htop' : t'.B 0 0 ≠ 0 := by
        rw [htopEq']
        exact htop
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        calc
          t'.B 0 0 = t.B 0 0 := htopEq'
          _ = normalize (t.B 0 0) := hnorm
          _ = normalize (t'.B 0 0) := by rw [htopEq']
      have hdiv' : ∀ j : Fin n, t'.B 0 0 ∣ t'.B 0 j.succ := by
        intro j
        simpa [t', hk'] using ih'.2 j
      refine ⟨?_, ?_⟩
      · calc
          (clearFirstRowByPivotLoop (k + 1) hk t).B 0 0
              = (clearFirstRowByPivotStepData t' jCurr).B 0 0 := by
                  rfl
          _ = t'.B 0 0 := by
                exact clearFirstRowByPivotStepData_topLeft t' jCurr htop' hnorm' (hdiv' jCurr)
          _ = t.B 0 0 := htopEq'
      · intro j
        by_cases hj : j = jCurr
        · subst hj
          rw [show (clearFirstRowByPivotLoop (k + 1) hk t).B 0 jCurr.succ =
              (clearFirstRowByPivotStepData t' jCurr).B 0 jCurr.succ by
                rfl]
          rw [clearFirstRowByPivotStepData_target_zero t' jCurr htop' hnorm' (hdiv' jCurr)]
          exact dvd_zero _
        · calc
            (clearFirstRowByPivotLoop (k + 1) hk t).B 0 0
                = (clearFirstRowByPivotStepData t' jCurr).B 0 0 := by
                    rfl
            _ = t'.B 0 0 := by
                  exact clearFirstRowByPivotStepData_topLeft t' jCurr htop' hnorm' (hdiv' jCurr)
            _ ∣ t'.B 0 j.succ := hdiv' j
            _ = (clearFirstRowByPivotStepData t' jCurr).B 0 j.succ := by
                  symm
                  exact clearFirstRowByPivotStepData_otherCol t' jCurr j htop' hnorm'
                    (hdiv' jCurr) hj 0
            _ = (clearFirstRowByPivotLoop (k + 1) hk t).B 0 j.succ := by
                  rfl


theorem clearFirstColumnByPivotLoop_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ i : Fin m, t.B 0 0 ∣ t.B i.succ 0) :
    (clearFirstColumnByPivotLoop k hk t).B 0 0 = t.B 0 0 :=
  (clearFirstColumnByPivotLoop_topLeft_colDivisible k hk t htop hnorm hdiv).1


theorem clearFirstColumnByPivotLoop_colDivisible {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ i : Fin m, t.B 0 0 ∣ t.B i.succ 0) :
    ∀ i : Fin m, (clearFirstColumnByPivotLoop k hk t).B 0 0 ∣
      (clearFirstColumnByPivotLoop k hk t).B i.succ 0 :=
  (clearFirstColumnByPivotLoop_topLeft_colDivisible k hk t htop hnorm hdiv).2


theorem clearFirstRowByPivotLoop_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ n) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ j : Fin n, t.B 0 0 ∣ t.B 0 j.succ) :
    (clearFirstRowByPivotLoop k hk t).B 0 0 = t.B 0 0 :=
  (clearFirstRowByPivotLoop_topLeft_rowDivisible k hk t htop hnorm hdiv).1


theorem clearFirstRowByPivotLoop_rowDivisible {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ n) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ j : Fin n, t.B 0 0 ∣ t.B 0 j.succ) :
    ∀ j : Fin n, (clearFirstRowByPivotLoop k hk t).B 0 0 ∣
      (clearFirstRowByPivotLoop k hk t).B 0 j.succ :=
  (clearFirstRowByPivotLoop_topLeft_rowDivisible k hk t htop hnorm hdiv).2


theorem clearFirstColumnByPivotLoop_topRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ i : Fin m, t.B 0 0 ∣ t.B i.succ 0)
    (j : Fin (n + 1)) :
    (clearFirstColumnByPivotLoop k hk t).B 0 j = t.B 0 j := by
  induction k generalizing t with
  | zero =>
      rfl
  | succ k ih =>
      let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnByPivotLoop k hk' t
      let iCurr : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have htopEq' := clearFirstColumnByPivotLoop_topLeft k hk' t htop hnorm hdiv
      have htop' : t'.B 0 0 ≠ 0 := by
        rw [htopEq']
        exact htop
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        calc
          t'.B 0 0 = t.B 0 0 := htopEq'
          _ = normalize (t.B 0 0) := hnorm
          _ = normalize (t'.B 0 0) := by rw [htopEq']
      have hdiv' : ∀ i : Fin m, t'.B 0 0 ∣ t'.B i.succ 0 := by
        intro i
        simpa [t', hk'] using
          clearFirstColumnByPivotLoop_colDivisible k hk' t htop hnorm hdiv i
      calc
        (clearFirstColumnByPivotLoop (k + 1) hk t).B 0 j
            = (clearFirstColumnByPivotStepData t' iCurr).B 0 j := by
                rfl
        _ = t'.B 0 j := by
              exact clearFirstColumnByPivotStepData_topRow t' iCurr htop' hnorm' (hdiv' iCurr) j
        _ = t.B 0 j := by
              simpa [t', hk'] using ih hk' t htop hnorm hdiv


theorem clearFirstColumnByPivotLoop_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ i : Fin m, t.B 0 0 ∣ t.B i.succ 0) :
    ∀ i : Fin m, i.1 < k -> (clearFirstColumnByPivotLoop k hk t).B i.succ 0 = 0 := by
  induction k generalizing t with
  | zero =>
      intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
  | succ k ih =>
      let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnByPivotLoop k hk' t
      let iCurr : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have htopEq' := clearFirstColumnByPivotLoop_topLeft k hk' t htop hnorm hdiv
      have htop' : t'.B 0 0 ≠ 0 := by
        rw [htopEq']
        exact htop
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        calc
          t'.B 0 0 = t.B 0 0 := htopEq'
          _ = normalize (t.B 0 0) := hnorm
          _ = normalize (t'.B 0 0) := by rw [htopEq']
      have hdiv' : ∀ i : Fin m, t'.B 0 0 ∣ t'.B i.succ 0 := by
        intro i
        simpa [t', hk'] using
          clearFirstColumnByPivotLoop_colDivisible k hk' t htop hnorm hdiv i
      intro i hi
      have hprefix' : ∀ j : Fin m, j.1 < iCurr.1 -> t'.B j.succ 0 = 0 := by
        intro j hj
        simpa [t', hk'] using ih hk' t htop hnorm hdiv j hj
      simpa [clearFirstColumnByPivotLoop, hk', t'] using
        clearFirstColumnByPivotStepData_prefix_zero t' iCurr htop' hnorm' (hdiv' iCurr)
          hprefix' i hi


theorem clearFirstRowByPivotLoop_firstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ n) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ j : Fin n, t.B 0 0 ∣ t.B 0 j.succ)
    (i : Fin (m + 1)) :
    (clearFirstRowByPivotLoop k hk t).B i 0 = t.B i 0 := by
  induction k generalizing t with
  | zero =>
      rfl
  | succ k ih =>
      let hk' : k ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstRowByPivotLoop k hk' t
      let jCurr : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have htopEq' := clearFirstRowByPivotLoop_topLeft k hk' t htop hnorm hdiv
      have htop' : t'.B 0 0 ≠ 0 := by
        rw [htopEq']
        exact htop
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        calc
          t'.B 0 0 = t.B 0 0 := htopEq'
          _ = normalize (t.B 0 0) := hnorm
          _ = normalize (t'.B 0 0) := by rw [htopEq']
      have hdiv' : ∀ j : Fin n, t'.B 0 0 ∣ t'.B 0 j.succ := by
        intro j
        simpa [t', hk'] using
          clearFirstRowByPivotLoop_rowDivisible k hk' t htop hnorm hdiv j
      calc
        (clearFirstRowByPivotLoop (k + 1) hk t).B i 0
            = (clearFirstRowByPivotStepData t' jCurr).B i 0 := by
                rfl
        _ = t'.B i 0 := by
              exact clearFirstRowByPivotStepData_firstCol t' jCurr htop' hnorm' (hdiv' jCurr) i
        _ = t.B i 0 := by
              simpa [t', hk'] using ih hk' t htop hnorm hdiv


theorem clearFirstRowByPivotLoop_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ n) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ j : Fin n, t.B 0 0 ∣ t.B 0 j.succ) :
    ∀ j : Fin n, j.1 < k -> (clearFirstRowByPivotLoop k hk t).B 0 j.succ = 0 := by
  induction k generalizing t with
  | zero =>
      intro j hj
      exact False.elim (Nat.not_lt_zero _ hj)
  | succ k ih =>
      let hk' : k ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstRowByPivotLoop k hk' t
      let jCurr : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have htopEq' := clearFirstRowByPivotLoop_topLeft k hk' t htop hnorm hdiv
      have htop' : t'.B 0 0 ≠ 0 := by
        rw [htopEq']
        exact htop
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        calc
          t'.B 0 0 = t.B 0 0 := htopEq'
          _ = normalize (t.B 0 0) := hnorm
          _ = normalize (t'.B 0 0) := by rw [htopEq']
      have hdiv' : ∀ j : Fin n, t'.B 0 0 ∣ t'.B 0 j.succ := by
        intro j
        simpa [t', hk'] using
          clearFirstRowByPivotLoop_rowDivisible k hk' t htop hnorm hdiv j
      intro j hj
      have hprefix' : ∀ c : Fin n, c.1 < jCurr.1 -> t'.B 0 c.succ = 0 := by
        intro c hc
        simpa [t', hk'] using ih hk' t htop hnorm hdiv c hc
      simpa [clearFirstRowByPivotLoop, hk', t'] using
        clearFirstRowByPivotStepData_prefix_zero t' jCurr htop' hnorm' (hdiv' jCurr)
          hprefix' j hj


def clearFirstColumnByPivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A)
    (hdiv : ∀ i : Fin m, s.t.B 0 0 ∣ s.t.B i.succ 0) :
    PivotState A :=
  let t := clearFirstColumnByPivotLoop m le_rfl s.t
  { t := t
    pivot_ne_zero := by
      rw [clearFirstColumnByPivotLoop_topLeft m le_rfl s.t s.pivot_ne_zero s.pivot_normalized hdiv]
      exact s.pivot_ne_zero
    pivot_normalized := by
      have htop : t.B 0 0 = s.t.B 0 0 :=
        clearFirstColumnByPivotLoop_topLeft m le_rfl s.t s.pivot_ne_zero s.pivot_normalized hdiv
      calc
        t.B 0 0 = s.t.B 0 0 := htop
        _ = normalize (s.t.B 0 0) := s.pivot_normalized
        _ = normalize (t.B 0 0) := by rw [htop] }


def clearFirstRowByPivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A)
    (_hcol : ∀ i : Fin m, s.t.B i.succ 0 = 0)
    (hdiv : ∀ j : Fin n, s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    PivotState A :=
  let t := clearFirstRowByPivotLoop n le_rfl s.t
  { t := t
    pivot_ne_zero := by
      rw [clearFirstRowByPivotLoop_topLeft n le_rfl s.t s.pivot_ne_zero s.pivot_normalized hdiv]
      exact s.pivot_ne_zero
    pivot_normalized := by
      have htop : t.B 0 0 = s.t.B 0 0 :=
        clearFirstRowByPivotLoop_topLeft n le_rfl s.t s.pivot_ne_zero s.pivot_normalized hdiv
      calc
        t.B 0 0 = s.t.B 0 0 := htop
        _ = normalize (s.t.B 0 0) := s.pivot_normalized
        _ = normalize (t.B 0 0) := by rw [htop] }


def clearLeadByPivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A)
    (hcolDiv : ∀ i : Fin m, s.t.B 0 0 ∣ s.t.B i.succ 0)
    (hrowDiv : ∀ j : Fin n, s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    LeadClearedState A := by
  let sCol := clearFirstColumnByPivot s hcolDiv
  have hcol : ∀ i : Fin m, sCol.t.B i.succ 0 = 0 := by
    intro i
    dsimp [sCol, clearFirstColumnByPivot]
    exact clearFirstColumnByPivotLoop_prefix_zero m le_rfl s.t s.pivot_ne_zero
      s.pivot_normalized hcolDiv i i.is_lt
  have hrowDiv' : ∀ j : Fin n, sCol.t.B 0 0 ∣ sCol.t.B 0 j.succ := by
    intro j
    dsimp [sCol, clearFirstColumnByPivot]
    rw [clearFirstColumnByPivotLoop_topLeft m le_rfl s.t s.pivot_ne_zero s.pivot_normalized hcolDiv,
      clearFirstColumnByPivotLoop_topRow m le_rfl s.t s.pivot_ne_zero s.pivot_normalized hcolDiv
        j.succ]
    exact hrowDiv j
  let sRow := clearFirstRowByPivot sCol hcol hrowDiv'
  refine sRow.toLeadClearedState ?_ ?_
  · intro j
    dsimp [sRow, clearFirstRowByPivot]
    exact clearFirstRowByPivotLoop_prefix_zero n le_rfl sCol.t sCol.pivot_ne_zero
      sCol.pivot_normalized hrowDiv' j j.is_lt
  · intro i
    dsimp [sRow, clearFirstRowByPivot]
    rw [clearFirstRowByPivotLoop_firstCol n le_rfl sCol.t sCol.pivot_ne_zero
      sCol.pivot_normalized hrowDiv' i.succ]
    exact hcol i


theorem clearLeadByPivot_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A)
    (hcolDiv : ∀ i : Fin m, s.t.B 0 0 ∣ s.t.B i.succ 0)
    (hrowDiv : ∀ j : Fin n, s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (clearLeadByPivot s hcolDiv hrowDiv).t.B 0 0 = s.t.B 0 0 := by
  let sCol := clearFirstColumnByPivot s hcolDiv
  have hcol : ∀ i : Fin m, sCol.t.B i.succ 0 = 0 := by
    intro i
    dsimp [sCol, clearFirstColumnByPivot]
    exact clearFirstColumnByPivotLoop_prefix_zero m le_rfl s.t s.pivot_ne_zero
      s.pivot_normalized hcolDiv i i.is_lt
  have hrowDiv' : ∀ j : Fin n, sCol.t.B 0 0 ∣ sCol.t.B 0 j.succ := by
    intro j
    dsimp [sCol, clearFirstColumnByPivot]
    rw [clearFirstColumnByPivotLoop_topLeft m le_rfl s.t s.pivot_ne_zero s.pivot_normalized hcolDiv,
      clearFirstColumnByPivotLoop_topRow m le_rfl s.t s.pivot_ne_zero s.pivot_normalized hcolDiv
        j.succ]
    exact hrowDiv j
  let sRow := clearFirstRowByPivot sCol hcol hrowDiv'
  have hrowTop : sRow.t.B 0 0 = sCol.t.B 0 0 := by
    dsimp [sRow, clearFirstRowByPivot]
    exact clearFirstRowByPivotLoop_topLeft n le_rfl sCol.t sCol.pivot_ne_zero
      sCol.pivot_normalized hrowDiv'
  have hcolTop : sCol.t.B 0 0 = s.t.B 0 0 := by
    dsimp [sCol, clearFirstColumnByPivot]
    exact clearFirstColumnByPivotLoop_topLeft m le_rfl s.t s.pivot_ne_zero
      s.pivot_normalized hcolDiv
  exact hrowTop.trans hcolTop


def stabilizePivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (state : PivotState A) :
    PivotDivisibleState A := by
  let μ : PivotState A -> Nat := fun s =>
    ComputableEuclideanOps.measure (s.t.B 0 0)
  let step :
      (state : PivotState A) ->
      ((next : PivotState A) -> μ next < μ state -> PivotDivisibleState A) ->
      PivotDivisibleState A := by
    intro state recurse
    cases m with
    | zero =>
        cases n with
        | zero =>
            let sClear := clearLeadByPivot state (fun i => Fin.elim0 i) (fun j => Fin.elim0 j)
            exact sClear.toPivotDivisibleState (fun i => Fin.elim0 i)
        | succ n =>
            cases hrow : firstUndivisibleFirstRow? state.t.B with
            | some j =>
                let next := prepareLeadRow state j
                  (firstUndivisibleFirstRow?_some_not_dvd state.t.B hrow)
                have hlt : μ next < μ state :=
                  prepareLeadRow_measure_lt state j
                    (firstUndivisibleFirstRow?_some_not_dvd state.t.B hrow)
                exact recurse next hlt
            | none =>
                let hcolDiv :
                    ∀ i : Fin 0, state.t.B 0 0 ∣ state.t.B i.succ 0 := by
                  intro i
                  exact Fin.elim0 i
                let hrowDiv := firstUndivisibleFirstRow?_eq_none state.t.B hrow
                let sClear := clearLeadByPivot state hcolDiv hrowDiv
                exact sClear.toPivotDivisibleState (fun i => Fin.elim0 i)
    | succ m =>
        cases n with
        | zero =>
            cases hcol : firstUndivisibleFirstCol? state.t.B with
            | some i =>
                let next := prepareLeadColumn state i
                  (firstUndivisibleFirstCol?_some_not_dvd state.t.B hcol)
                have hlt : μ next < μ state :=
                  prepareLeadColumn_measure_lt state i
                    (firstUndivisibleFirstCol?_some_not_dvd state.t.B hcol)
                exact recurse next hlt
            | none =>
                let hcolDiv := firstUndivisibleFirstCol?_eq_none state.t.B hcol
                let hrowDiv :
                    ∀ j : Fin 0, state.t.B 0 0 ∣ state.t.B 0 j.succ := by
                  intro j
                  exact Fin.elim0 j
                let sClear := clearLeadByPivot state hcolDiv hrowDiv
                exact sClear.toPivotDivisibleState (fun i j => Fin.elim0 j)
        | succ n =>
            cases hcol : firstUndivisibleFirstCol? state.t.B with
            | some i =>
                let next := prepareLeadColumn state i
                  (firstUndivisibleFirstCol?_some_not_dvd state.t.B hcol)
                have hlt : μ next < μ state :=
                  prepareLeadColumn_measure_lt state i
                    (firstUndivisibleFirstCol?_some_not_dvd state.t.B hcol)
                exact recurse next hlt
            | none =>
                cases hrow : firstUndivisibleFirstRow? state.t.B with
                | some j =>
                    let next := prepareLeadRow state j
                      (firstUndivisibleFirstRow?_some_not_dvd state.t.B hrow)
                    have hlt : μ next < μ state :=
                      prepareLeadRow_measure_lt state j
                        (firstUndivisibleFirstRow?_some_not_dvd state.t.B hrow)
                    exact recurse next hlt
                | none =>
                    let hcolDiv := firstUndivisibleFirstCol?_eq_none state.t.B hcol
                    let hrowDiv := firstUndivisibleFirstRow?_eq_none state.t.B hrow
                    let sClear := clearLeadByPivot state hcolDiv hrowDiv
                    cases hlower :
                        firstUndivisibleLowerRightWithOps?
                          sClear.t.B (sClear.t.B 0 0) with
                    | some p =>
                        have hbad :=
                          firstUndivisibleLowerRightWithOps?_some_not_dvd
                            sClear.t.B (sClear.t.B 0 0) hlower
                        let next := improvePivot sClear p.1 p.2
                          hbad
                        have hlt : μ next < μ state := by
                          dsimp [μ, next]
                          rw [← clearLeadByPivot_topLeft state hcolDiv hrowDiv]
                          exact improvePivot_measure_lt sClear p.1 p.2
                            hbad
                        exact recurse next hlt
                    | none =>
                        exact sClear.toPivotDivisibleState <|
                          firstUndivisibleLowerRightWithOps?_eq_none
                            sClear.t.B (sClear.t.B 0 0) hlower
  exact (measure μ).wf.fix step state


end Internal

open Internal

/-- Constructive Smith kernel; recursive state and helpers remain module-private. -/
public def smithNormalFormFin {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    [ComputableEuclideanOps R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : SNFResultFin A := by
  induction m generalizing n with
  | zero =>
      refine
        { U := 1
          U_cert := MatrixInverseCertificate.one
          S := A
          V := 1
          V_cert := MatrixInverseCertificate.one
          equation :=
            NormalForms.Matrix.Constructive.one_mul_mul_one A
          isSmith := IsSmithNormalFormFin.emptyRows _ }
  | succ m ih =>
      cases n with
      | zero =>
          refine
            { U := 1
              U_cert := MatrixInverseCertificate.one
              S := A
              V := 1
              V_cert := MatrixInverseCertificate.one
              equation :=
                NormalForms.Matrix.Constructive.one_mul_mul_one A
              isSmith := IsSmithNormalFormFin.emptyCols _ }
      | succ n =>
          cases hentry : firstNonzeroEntryWithOps? A with
          | none =>
            have hA : A = 0 := by
              apply firstNonzeroEntry?_eq_none A
              simpa using hentry
            refine
              { U := 1
                U_cert := MatrixInverseCertificate.one
                S := A
                V := 1
                V_cert := MatrixInverseCertificate.one
                equation :=
                  NormalForms.Matrix.Constructive.one_mul_mul_one A
                isSmith := ?_ }
            simpa [hA] using
              (zeroSmith (m := m + 1) (n := n + 1) (R := R))
          | some p =>
            have hp : A p.1 p.2 ≠ 0 := by
              apply firstNonzeroEntry?_some_ne_zero A
              simpa using hentry
            let state0 := initPivotFromEntry A p hp
            let state := stabilizePivot state0
            let lowerRes := ih (n := n) (lowerRight state.t.B)
            let tLiftLeft :=
              TwoSidedTransform.diagLiftLeft state.t.B lowerRes.U lowerRes.U_cert
            let tAfterLeft := state.t.trans tLiftLeft
            let tLiftRight :=
              TwoSidedTransform.diagLiftRight tAfterLeft.B lowerRes.V lowerRes.V_cert
            let tFinal := tAfterLeft.trans tLiftRight
            have hAfterLeftTopLeft : tAfterLeft.B 0 0 = state.t.B 0 0 := by
              simp [tAfterLeft, tLiftLeft, TwoSidedTransform.diagLiftLeft, TwoSidedTransform.trans,
                diagLiftMatrix_mul_topRow]
            have hAfterLeftRow : ∀ j : Fin n, tAfterLeft.B 0 j.succ = 0 := by
              intro j
              simpa [tAfterLeft, tLiftLeft, TwoSidedTransform.diagLiftLeft,
                TwoSidedTransform.trans, diagLiftMatrix_mul_topRow] using state.rowCleared j
            have hAfterLeftCol : ∀ i : Fin m, tAfterLeft.B i.succ 0 = 0 := by
              intro i
              simpa [tAfterLeft, tLiftLeft, TwoSidedTransform.diagLiftLeft,
                TwoSidedTransform.trans] using
                diagLiftMatrix_mul_zero_firstCol (A := state.t.B) lowerRes.U state.colCleared i
            have hFinalTopLeft : tFinal.B 0 0 = state.t.B 0 0 := by
              simp [tFinal, tLiftRight, TwoSidedTransform.diagLiftRight, TwoSidedTransform.trans,
                hAfterLeftTopLeft]
            have hFinalRow : ∀ j : Fin n, tFinal.B 0 j.succ = 0 := by
              intro j
              simpa [tFinal, tLiftRight, TwoSidedTransform.diagLiftRight,
                TwoSidedTransform.trans] using
                zero_topRow_mul_diagLiftMatrix (A := tAfterLeft.B) lowerRes.V hAfterLeftRow j
            have hFinalCol : ∀ i : Fin m, tFinal.B i.succ 0 = 0 := by
              intro i
              have hfirstCol : tFinal.B i.succ 0 = tAfterLeft.B i.succ 0 := by
                change
                  (tAfterLeft.B * diagLiftMatrix lowerRes.V) i.succ 0 =
                    tAfterLeft.B i.succ 0
                exact mul_diagLiftMatrix_firstCol tAfterLeft.B lowerRes.V i.succ
              rw [hfirstCol]
              exact hAfterLeftCol i
            have hFinalLower : lowerRight tFinal.B = lowerRes.S := by
              calc
                lowerRight tFinal.B
                    = lowerRight (tAfterLeft.B * diagLiftMatrix lowerRes.V) := by
                        rfl
                _ = lowerRight tAfterLeft.B * lowerRes.V := by
                      exact lowerRight_mul_diagLiftMatrix tAfterLeft.B lowerRes.V
                _ = (lowerRes.U * lowerRight state.t.B) * lowerRes.V := by
                      simp [tAfterLeft, tLiftLeft, TwoSidedTransform.diagLiftLeft,
                        TwoSidedTransform.trans, lowerRight_diagLiftMatrix_mul]
                _ = lowerRes.S := by
                      simpa only [NormalForms.Matrix.Constructive.mul_assoc] using
                        lowerRes.equation
            have hFinalDiv : ∀ i : Fin m, ∀ j : Fin n, tFinal.B 0 0 ∣ tFinal.B i.succ j.succ := by
              intro i j
              rw [hFinalTopLeft]
              have hLeft :
                  ∀ r s, state.t.B 0 0 ∣
                    (lowerRes.U * lowerRight state.t.B) r s := by
                exact dvd_matrix_mul_of_right state.lowerRightDivisible
              have hRight :
                  ∀ r s, state.t.B 0 0 ∣
                    ((lowerRes.U * lowerRight state.t.B) * lowerRes.V) r s := by
                exact dvd_matrix_mul_of_left hLeft
              have hEq :
                  tFinal.B i.succ j.succ =
                    ((lowerRes.U * lowerRight state.t.B) * lowerRes.V) i j := by
                calc
                  tFinal.B i.succ j.succ = (lowerRight tFinal.B) i j := by rfl
                  _ = lowerRes.S i j := by rw [hFinalLower]
                  _ = ((lowerRes.U * lowerRight state.t.B) * lowerRes.V) i j := by
                        rw [lowerRes.equation]
              rw [hEq]
              exact hRight i j
            refine
              { U := tFinal.U
                U_cert := tFinal.U_cert
                S := tFinal.B
                V := tFinal.V
                V_cert := tFinal.V_cert
                equation := tFinal.two_sided_mul
                isSmith := ?_ }
            refine IsSmithNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_ ?_
            · rw [hFinalTopLeft]
              exact state.pivot_ne_zero
            · rw [hFinalTopLeft]
              exact state.pivot_normalized
            · exact hFinalRow
            · exact hFinalCol
            · simpa [hFinalLower] using lowerRes.isSmith
            · exact hFinalDiv

end NormalForms.Matrix.Smith
