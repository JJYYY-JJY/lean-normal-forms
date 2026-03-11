import NormalForms.Matrix.Certificates
import NormalForms.Matrix.Hermite.Basic

/-!
# Smith Normal Form API

Two-sided Smith normal forms over Euclidean domains.

This module exposes the public Smith predicate, invariant-factor reader, and
certificate/result packaging API over arbitrary finite index types by reindexing
through `Fintype.equivFin`.

That bridge is intentionally kept proof-oriented rather than simplification-
oriented: we do not register `[simp]` lemmas that force `reindex
(Fintype.equivFin _)` back to definitional identity on `Fin`. In practice those
lemmas can trigger very expensive definitional-equality search for matrix blocks
and `Fin` coercions. Concrete diagonal-specification and invariant-factor smoke
tests therefore live on the internal `Fin` layer, while the public layer focuses
on stable packaging theorems such as `SNFResult.ofCertificate`.

Internally, the current Phase 3 implementation already includes a verified
same-size lead-clearing foundation together with the next raw same-size layer:
pivot-state records, pure-data first-column/first-row clearing loops, external
invariance lemmas ending in `clearLeadByPivot`, row/column `prepareLead...`
wrappers, and a single-step nondivisible `improvePivot` interface with a strict
descent theorem. The missing pieces are still the alternating/stabilization
driver around those raw steps and the outer recursive executable Smith kernel.
-/

namespace NormalForms.Matrix.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

namespace Internal

def diagEntry {m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin m) (Fin n) R) (k : Nat)
    (hk : k < Nat.min m n) : R :=
  A ⟨k, Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)⟩
    ⟨k, Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩


def offDiagZero {m n : Nat} {R : Type _} [Zero R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ i j, i.1 ≠ j.1 -> A i j = 0


def diagNormalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ k (hk : k < Nat.min m n), diagEntry A k hk = normalize (diagEntry A k hk)


def diagChain {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ k (hk : k + 1 < Nat.min m n),
    diagEntry A k (Nat.lt_trans (Nat.lt_succ_self k) hk) ∣
      diagEntry A (k + 1) hk


def IsSmithNormalFormDiag {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  offDiagZero A ∧ diagNormalized A ∧ diagChain A


noncomputable instance {m n : Nat} {R : Type _} [Zero R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (offDiagZero A) := by
  classical
  unfold offDiagZero
  infer_instance


noncomputable instance {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (diagNormalized A) := by
  classical
  unfold diagNormalized diagEntry
  infer_instance


noncomputable instance {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (diagChain A) := by
  classical
  infer_instance


noncomputable instance {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (IsSmithNormalFormDiag A) := by
  classical
  unfold IsSmithNormalFormDiag
  infer_instance


inductive IsSmithNormalFormFin {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
    {m n : Nat} -> _root_.Matrix (Fin m) (Fin n) R -> Prop
  | emptyRows {n : Nat} (A : _root_.Matrix (Fin 0) (Fin n) R) :
      IsSmithNormalFormFin A
  | emptyCols {m : Nat} (A : _root_.Matrix (Fin m) (Fin 0) R) :
      IsSmithNormalFormFin A
  | zeroLead {m n : Nat} (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
      (hzero : A 0 0 = 0)
      (hrow : ∀ j : Fin n, A 0 j.succ = 0)
      (hcol : ∀ i : Fin m, A i.succ 0 = 0)
      (hLowerZero : lowerRight A = 0) :
      IsSmithNormalFormFin A
  | pivot {m n : Nat} (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
      (hpivot : A 0 0 ≠ 0)
      (hnorm : A 0 0 = normalize (A 0 0))
      (hrow : ∀ j : Fin n, A 0 j.succ = 0)
      (hcol : ∀ i : Fin m, A i.succ 0 = 0)
      (hLower : IsSmithNormalFormFin (lowerRight A))
      (hdiv : ∀ i : Fin m, ∀ j : Fin n, A 0 0 ∣ A i.succ j.succ) :
      IsSmithNormalFormFin A

structure FinSNFResult {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) where
  U : _root_.Matrix (Fin m) (Fin m) R
  S : _root_.Matrix (Fin m) (Fin n) R
  V : _root_.Matrix (Fin n) (Fin n) R
  two_sided_mul : U * A * V = S
  leftUnimodular : Unimodular U
  rightUnimodular : Unimodular V
  isSmith : IsSmithNormalFormFin S


def firstNonzeroEntry? {m n : Nat} {R : Type _}
    [Zero R] [DecidableEq R] :
    _root_.Matrix (Fin m) (Fin n) R -> Option (Fin m × Fin n)
  | A =>
      let rec goRows : (k : Nat) -> k ≤ m -> Option (Fin m × Fin n)
        | 0, _ => none
        | k + 1, hk =>
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            match goRows k hk' with
            | some p => some p
            | none =>
                let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                match firstNonzero? (fun j : Fin n => A i j) with
                | none => none
                | some j => some (i, j)
      goRows m (Nat.le_refl _)


theorem firstNonzeroEntry?_eq_none {m n : Nat} {R : Type _}
    [Zero R] [DecidableEq R] :
    ∀ (A : _root_.Matrix (Fin m) (Fin n) R),
      firstNonzeroEntry? A = none -> A = 0
  | A, hnone => by
      ext i j
      unfold firstNonzeroEntry? at hnone
      have hnone' : firstNonzeroEntry?.goRows A m (Nat.le_refl m) = none := by
        simpa [firstNonzeroEntry?] using hnone
      clear hnone
      let rowWitness : ∀ k (hk : k ≤ m),
          firstNonzeroEntry?.goRows A k hk = none ->
            ∀ i' : Fin m, i'.1 < k -> ∀ j' : Fin n, A i' j' = 0 := by
        intro k
        induction k with
        | zero =>
            intro hk hgo i' hi
            exact False.elim (Nat.not_lt_zero _ hi)
        | succ k ih =>
            intro hk hgo i' hi j'
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            have hsplit :
                (match firstNonzeroEntry?.goRows A k hk' with
                | some p => some p
                | none =>
                    let i0 : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                    match firstNonzero? (fun s : Fin n => A i0 s) with
                    | none => none
                    | some j0 => some (i0, j0)) = none := by
              simpa [firstNonzeroEntry?] using hgo
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hEq
            · have hgo' : firstNonzeroEntry?.goRows A k hk' = none := by
                cases hgoRows : firstNonzeroEntry?.goRows A k hk' with
                | none =>
                    rfl
                | some p =>
                    simp [hgoRows] at hsplit
              exact ih hk' hgo' i' hi' j'
            · have : i' = ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ := Fin.ext hEq
              subst this
              cases hrow : firstNonzero? (fun s : Fin n => A ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ s) with
              | none =>
                  exact firstNonzero?_eq_none _ hrow j'
              | some p =>
                  have : False := by
                    cases hgoRows : firstNonzeroEntry?.goRows A k hk' with
                    | none =>
                        simp [hgoRows, hrow] at hsplit
                    | some q =>
                        simp [hgoRows] at hsplit
                  exact False.elim this
      exact rowWitness m (Nat.le_refl m) hnone' i i.is_lt j


theorem firstNonzeroEntry?_some_ne_zero {m n : Nat} {R : Type _}
    [Zero R] [DecidableEq R] :
    ∀ (A : _root_.Matrix (Fin m) (Fin n) R) {p : Fin m × Fin n},
      firstNonzeroEntry? A = some p -> A p.1 p.2 ≠ 0
  | A, p, hsome => by
      unfold firstNonzeroEntry? at hsome
      have hsome' : firstNonzeroEntry?.goRows A m (Nat.le_refl m) = some p := by
        simpa [firstNonzeroEntry?] using hsome
      clear hsome
      let rowWitness : ∀ k (hk : k ≤ m) {p : Fin m × Fin n},
          firstNonzeroEntry?.goRows A k hk = some p -> A p.1 p.2 ≠ 0 := by
        intro k
        induction k with
        | zero =>
            intro hk p h
            simpa [firstNonzeroEntry?.goRows] using h
        | succ k ih =>
            intro hk p h
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            cases hgo : firstNonzeroEntry?.goRows A k hk' with
            | some q =>
                simp [firstNonzeroEntry?.goRows, hgo] at h
                cases h
                exact ih hk' hgo
            | none =>
                let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                cases hrow : firstNonzero? (fun j : Fin n => A i j) with
                | none =>
                    have : none = some p := by
                      simpa [firstNonzeroEntry?.goRows, hgo, i, hrow] using h
                    cases this
                | some j =>
                    have h' : some (i, j) = some p := by
                      simpa [firstNonzeroEntry?.goRows, hgo, i, hrow] using h
                    cases h'
                    exact firstNonzero?_some_ne_zero (fun s : Fin n => A i s) hrow
      exact rowWitness m (Nat.le_refl m) hsome'


def firstUndivisible? {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    {n : Nat} -> R -> (Fin n -> R) -> Option (Fin n)
  | 0, _, _ => none
  | _ + 1, d, row =>
      if hmod : row 0 % d = 0 then
        Option.map Fin.succ (firstUndivisible? d fun j => row j.succ)
      else
        some 0


theorem firstUndivisible?_eq_none {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    {n : Nat} -> (d : R) -> (row : Fin n -> R) ->
      firstUndivisible? d row = none -> ∀ i, d ∣ row i
  | 0, _, _, _, i => Fin.elim0 i
  | _ + 1, d, row, hnone, i => by
      by_cases hmod : row 0 % d = 0
      · rw [firstUndivisible?, hmod] at hnone
        have htail : firstUndivisible? d (fun k => row k.succ) = none := by
          simpa using hnone
        cases i using Fin.cases with
        | zero =>
            exact (EuclideanDomain.mod_eq_zero).1 hmod
        | succ j =>
            exact firstUndivisible?_eq_none d (fun k => row k.succ) htail j
      · simp [firstUndivisible?, hmod] at hnone


theorem firstUndivisible?_some_not_dvd {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    {n : Nat} -> (d : R) -> (row : Fin n -> R) -> {i : Fin n} ->
      firstUndivisible? d row = some i -> ¬ d ∣ row i
  | 0, _, _, i, _ => Fin.elim0 i
  | _ + 1, d, row, i, hsome => by
      by_cases hmod : row 0 % d = 0
      · rw [firstUndivisible?, hmod] at hsome
        cases i using Fin.cases with
        | zero =>
            simp at hsome
        | succ j =>
            cases htail : firstUndivisible? d (fun k => row k.succ) with
            | none =>
                simp [htail] at hsome
            | some j' =>
                simp [htail] at hsome
                subst hsome
                exact firstUndivisible?_some_not_dvd d (fun k => row k.succ) htail
      · cases i using Fin.cases with
        | zero =>
            simpa [EuclideanDomain.mod_eq_zero] using hmod
        | succ j =>
            have hzero : firstUndivisible? d row = some (0 : Fin (_ + 1)) := by
              simp [firstUndivisible?, hmod]
            have : (0 : Fin (_ + 1)) = j.succ := by
              simpa using hzero.symm.trans hsome
            exact False.elim (Fin.succ_ne_zero _ this.symm)


def firstUndivisibleLowerRight? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R -> R -> Option (Fin m × Fin n)
  | A, d =>
      let rec goRows : (k : Nat) -> k ≤ m -> Option (Fin m × Fin n)
        | 0, _ => none
        | k + 1, hk =>
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            match goRows k hk' with
            | some p => some p
            | none =>
                let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                match firstUndivisible? d (fun j : Fin n => A i.succ j.succ) with
                | none => none
                | some j => some (i, j)
      goRows m (Nat.le_refl _)

def invariantFactors {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
    {m n : Nat} -> _root_.Matrix (Fin m) (Fin n) R -> List R
  | 0, _, _ => []
  | _, 0, _ => []
  | _ + 1, _ + 1, A =>
      let d := normalize (A 0 0)
      if d = 0 then
        []
      else
        d :: invariantFactors (lowerRight A)


@[simp] theorem invariantFactors_emptyRows {n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin 0) (Fin n) R) :
    invariantFactors A = [] := by
  simp [invariantFactors]


@[simp] theorem invariantFactors_emptyCols {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin 0) R) :
    invariantFactors A = [] := by
  cases m <;> simp [invariantFactors]


@[simp] theorem invariantFactors_zeroLead {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hzero : A 0 0 = 0) :
    invariantFactors A = [] := by
  simp [invariantFactors, hzero]


@[simp] theorem invariantFactors_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hpivot : A 0 0 ≠ 0)
    (hnorm : A 0 0 = normalize (A 0 0)) :
    invariantFactors A = A 0 0 :: invariantFactors (lowerRight A) := by
  have hnormNe : normalize (A 0 0) ≠ 0 := by
    rw [← hnorm]
    exact hpivot
  dsimp [invariantFactors]
  rw [if_neg hnormNe]
  rw [← hnorm]


private theorem diagEntry_lowerRight {m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (k : Nat) (hk : k < Nat.min m n) :
    diagEntry (lowerRight A) k hk =
      diagEntry A (k + 1)
        ((lt_min_iff).2
          ⟨Nat.succ_lt_succ ((lt_min_iff).1 hk).1,
            Nat.succ_lt_succ ((lt_min_iff).1 hk).2⟩) := by
  simp [diagEntry, lowerRight]


private theorem lt_min_of_succ_lt_min_succ {a b k : Nat}
    (hk : k + 1 < Nat.min (a + 1) (b + 1)) :
    k < Nat.min a b := by
  refine (lt_min_iff).2 ⟨?_, ?_⟩
  · exact Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).1
  · exact Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).2


private theorem two_lt_min_succ_of_lt_min {a b k : Nat}
    (hk : k + 1 < Nat.min a b) :
    k + 2 < Nat.min (a + 1) (b + 1) := by
  refine (lt_min_iff).2 ⟨?_, ?_⟩
  · exact Nat.succ_lt_succ ((lt_min_iff).1 hk).1
  · exact Nat.succ_lt_succ ((lt_min_iff).1 hk).2


private theorem offDiagZero_lowerRight {m n : Nat} {R : Type _} [Zero R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : offDiagZero A) :
    offDiagZero (lowerRight A) := by
  intro i j hij
  exact hA i.succ j.succ (by
    intro hEq
    exact hij (Nat.succ.inj hEq))


private theorem diagNormalized_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : diagNormalized A) :
    diagNormalized (lowerRight A) := by
  intro k hk
  rw [diagEntry_lowerRight]
  exact hA (k + 1) ((lt_min_iff).2
    ⟨Nat.succ_lt_succ ((lt_min_iff).1 hk).1,
      Nat.succ_lt_succ ((lt_min_iff).1 hk).2⟩)


private theorem diagChain_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : diagChain A) :
    diagChain (lowerRight A) := by
  intro k hk
  rw [diagEntry_lowerRight, diagEntry_lowerRight]
  exact hA (k + 1) (two_lt_min_succ_of_lt_min hk)


theorem isSmithNormalFormFin_toDiag {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A) :
    IsSmithNormalFormDiag A := by
  induction hA
  case emptyRows A =>
      refine ⟨?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro k hk
        simpa using hk
      · intro k hk
        simpa using hk
  case emptyCols A =>
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        exact Fin.elim0 j
      · intro k hk
        simpa using hk
      · intro k hk
        simpa using hk
  case zeroLead m' n' A hzero hrow hcol hLowerZero =>
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero =>
                exact False.elim (hij rfl)
            | succ j =>
                exact hrow j
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                exact hcol i
            | succ j =>
                simpa [lowerRight] using congrFun (congrFun hLowerZero i) j
      · intro k hk
        cases k with
        | zero =>
            simpa [diagEntry, hzero]
        | succ k =>
            have hk' : k < Nat.min m' n' := lt_min_of_succ_lt_min_succ hk
            rw [← diagEntry_lowerRight (A := A) k hk']
            simp [hLowerZero, diagEntry]
      · intro k hk
        cases k with
        | zero =>
            have hk' : 0 < Nat.min m' n' := lt_min_of_succ_lt_min_succ hk
            have hRight : diagEntry A 1 hk = 0 := by
              rw [← diagEntry_lowerRight (A := A) 0 hk']
              simp [hLowerZero, diagEntry]
            simpa [diagEntry, hzero] using hRight
        | succ k =>
            have hkMid : k + 1 < Nat.min (m' + 1) (n' + 1) :=
              Nat.lt_trans (Nat.lt_succ_self (k + 1)) hk
            have hkLeft : k < Nat.min m' n' := lt_min_of_succ_lt_min_succ hkMid
            have hkRight : k + 1 < Nat.min m' n' := lt_min_of_succ_lt_min_succ hk
            rw [← diagEntry_lowerRight (A := A) k hkLeft]
            rw [← diagEntry_lowerRight (A := A) (k + 1) hkRight]
            simp [hLowerZero, diagEntry]
  case pivot m' n' A hpivot hnorm hrow hcol hLower hdiv ih =>
      rcases ih with ⟨hOffLower, hNormLower, hChainLower⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero =>
                exact False.elim (hij rfl)
            | succ j =>
                exact hrow j
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                exact hcol i
            | succ j =>
                exact hOffLower i j (by
                  intro hEq
                  exact hij (by simpa [hEq]))
      · intro k hk
        cases k with
        | zero =>
            simpa [diagEntry] using hnorm
        | succ k =>
            simpa [diagEntry_lowerRight] using
              hNormLower k (lt_min_of_succ_lt_min_succ hk)
      · intro k hk
        cases k with
        | zero =>
            have hm : 0 < m' := Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).1
            have hn : 0 < n' := Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).2
            let i0 : Fin m' := ⟨0, hm⟩
            let j0 : Fin n' := ⟨0, hn⟩
            simpa [diagEntry, i0, j0] using hdiv i0 j0
        | succ k =>
            simpa [diagEntry_lowerRight] using
              hChainLower k (lt_min_of_succ_lt_min_succ hk)


private theorem zeroSmith {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
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

/-- The bridge-side submodule attached to a matrix: its column span. -/
def smithColumnSpan {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R]
    (A : _root_.Matrix m n R) : Submodule R (m -> R) :=
  LinearMap.range A.mulVecLin


/-- Read normalized nonzero diagonal entries from a Smith matrix, truncating at the first `0`.

The public wrapper works for arbitrary finite index types by reindexing to
`Fin`. We intentionally avoid a companion `[simp]` bridge lemma for `Fin`
matrices, since expanding `Fintype.equivFin` aggressively can make elaboration
pathologically slow.
-/
noncomputable def smithInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : List R :=
  Internal.invariantFactors
    (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)

/-- Public Smith-normal-form predicate.

Like `smithInvariantFactors`, this wrapper is defined by reindexing to the
internal `Fin` predicate. Callers should not expect `simp` to compute through
that bridge automatically; use the internal predicate for concrete executable
smoke checks, and use this public predicate for API-level statements.
-/
def IsSmithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : Prop :=
  Internal.IsSmithNormalFormDiag
    (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)

noncomputable instance {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} : Decidable (IsSmithNormalForm A) := by
  classical
  unfold IsSmithNormalForm
  infer_instance



theorem unimodular_transpose {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    {U : _root_.Matrix m m R} (hU : Unimodular U) :
    Unimodular U.transpose := by
  simpa [Unimodular, _root_.Matrix.det_transpose] using hU


structure TwoSidedTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  B : _root_.Matrix m n R
  V : _root_.Matrix n n R
  two_sided_mul : U * A * V = B
  leftUnimodular : Unimodular U
  rightUnimodular : Unimodular V


def TwoSidedTransform.refl {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) : TwoSidedTransform A :=
  { U := 1
    B := A
    V := 1
    two_sided_mul := by simp
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_one }


def TwoSidedTransform.trans {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R}
    (first : TwoSidedTransform A) (second : TwoSidedTransform first.B) :
    TwoSidedTransform A :=
  { U := second.U * first.U
    B := second.B
    V := first.V * second.V
    two_sided_mul := by
      calc
        (second.U * first.U) * A * (first.V * second.V)
            = second.U * (first.U * A * first.V) * second.V := by
                simp [Matrix.mul_assoc]
        _ = second.U * first.B * second.V := by
              rw [first.two_sided_mul]
        _ = second.B := second.two_sided_mul
    leftUnimodular := unimodular_mul second.leftUnimodular first.leftUnimodular
    rightUnimodular := unimodular_mul first.rightUnimodular second.rightUnimodular }


def TwoSidedTransform.ofLeftTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (t : LeftTransform A) :
    TwoSidedTransform A :=
  { U := t.U
    B := t.B
    V := 1
    two_sided_mul := by simpa using t.left_mul
    leftUnimodular := t.unimodular
    rightUnimodular := unimodular_one }


def TwoSidedTransform.ofTransposeLeftTransform {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} (t : LeftTransform A.transpose) :
    TwoSidedTransform A :=
  { U := 1
    B := t.B.transpose
    V := t.U.transpose
    two_sided_mul := by
      have h := congrArg _root_.Matrix.transpose t.left_mul
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_transpose t.unimodular }


def TwoSidedTransform.swapRows {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i j : m) : TwoSidedTransform A :=
  { U := rowOperationMatrix (.swap i j)
    B := applyRowOperation A (.swap i j)
    V := 1
    two_sided_mul := by
      simp [rowOperationMatrix_mul]
    leftUnimodular := unimodular_rowOperationMatrix (.swap i j) (by trivial)
    rightUnimodular := unimodular_one }


def TwoSidedTransform.swapCols {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i j : n) : TwoSidedTransform A :=
  { U := 1
    B := applyColumnOperation A (.swap i j)
    V := columnOperationMatrix (.swap i j)
    two_sided_mul := by
      simp [mul_columnOperationMatrix]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_columnOperationMatrix (.swap i j) (by trivial) }


def TwoSidedTransform.addRows {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : m) (c : R) (hne : src ≠ dst) :
    TwoSidedTransform A :=
  { U := rowOperationMatrix (.add src dst c)
    B := applyRowOperation A (.add src dst c)
    V := 1
    two_sided_mul := by
      simp [rowOperationMatrix_mul]
    leftUnimodular := unimodular_rowOperationMatrix (.add src dst c) hne
    rightUnimodular := unimodular_one }


def TwoSidedTransform.addCols {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : n) (c : R) (hne : src ≠ dst) :
    TwoSidedTransform A :=
  { U := 1
    B := applyColumnOperation A (.add src dst c)
    V := columnOperationMatrix (.add src dst c)
    two_sided_mul := by
      simp [mul_columnOperationMatrix]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_columnOperationMatrix (.add src dst c) hne }


def TwoSidedTransform.unitSmulRow {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i : m) (c : R) (hc : IsUnit c) :
    TwoSidedTransform A :=
  { U := rowOperationMatrix (.smul i c)
    B := applyRowOperation A (.smul i c)
    V := 1
    two_sided_mul := by
      simp [rowOperationMatrix_mul]
    leftUnimodular := unimodular_rowOperationMatrix (.smul i c) hc
    rightUnimodular := unimodular_one }


def TwoSidedTransform.unitSmulCol {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i : n) (c : R) (hc : IsUnit c) :
    TwoSidedTransform A :=
  { U := 1
    B := applyColumnOperation A (.smul i c)
    V := columnOperationMatrix (.smul i c)
    two_sided_mul := by
      simp [mul_columnOperationMatrix]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_columnOperationMatrix (.smul i c) hc }


def TwoSidedTransform.diagLiftLeft {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) (hU : Unimodular U) :
    TwoSidedTransform A :=
  { U := diagLiftMatrix U
    B := diagLiftMatrix U * A
    V := 1
    two_sided_mul := by simp [Matrix.mul_assoc]
    leftUnimodular := unimodular_diagLiftMatrix hU
    rightUnimodular := unimodular_one }


def TwoSidedTransform.diagLiftRight {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (V : _root_.Matrix (Fin n) (Fin n) R) (hV : Unimodular V) :
    TwoSidedTransform A :=
  { U := 1
    B := A * diagLiftMatrix V
    V := diagLiftMatrix V
    two_sided_mul := by simp [Matrix.mul_assoc]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_diagLiftMatrix hV }

private theorem mod_ne_zero_of_not_dvd {R : Type _} [EuclideanDomain R]
    {a b : R} (ha : a ≠ 0) (hnot : ¬ a ∣ b) :
    b % a ≠ 0 := by
  intro hmod
  exact hnot ((EuclideanDomain.mod_eq_zero).1 hmod)


private theorem gcd_dvd_mod {R : Type _} [EuclideanDomain R] [DecidableEq R]
    {a b : R} :
    EuclideanDomain.gcd a b ∣ b % a := by
  exact (EuclideanDomain.dvd_mod_iff (EuclideanDomain.gcd_dvd_left a b)).2
    (EuclideanDomain.gcd_dvd_right a b)


private theorem normalize_gcd_dvd_left {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {a b : R} :
    normalize (EuclideanDomain.gcd a b) ∣ a :=
  (normalize_dvd_iff).2 (EuclideanDomain.gcd_dvd_left a b)


private theorem normalize_gcd_dvd_right {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {a b : R} :
    normalize (EuclideanDomain.gcd a b) ∣ b :=
  (normalize_dvd_iff).2 (EuclideanDomain.gcd_dvd_right a b)

namespace Internal

structure PivotState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) where
  t : TwoSidedTransform A
  pivot_ne_zero : t.B 0 0 ≠ 0
  pivot_normalized : t.B 0 0 = normalize (t.B 0 0)


def initPivotFromEntry {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (p : Fin (m + 1) × Fin (n + 1)) (hp : A p.1 p.2 ≠ 0) :
    PivotState A := by
  let tRow := TwoSidedTransform.swapRows A p.1 0
  let tCol := tRow.trans (TwoSidedTransform.swapCols tRow.B p.2 0)
  let tNorm :=
    tCol.trans
      (TwoSidedTransform.unitSmulRow tCol.B 0 (normUnit (tCol.B 0 0) : R)
        (normUnit (tCol.B 0 0)).isUnit)
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
    exact (normalize_idem (A p.1 p.2)).symm


def initPivotState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (hA : A ≠ 0) :
    PivotState A := by
  cases hentry : firstNonzeroEntry? A with
  | none =>
      exact False.elim (hA (firstNonzeroEntry?_eq_none A hentry))
  | some p =>
      exact initPivotFromEntry A p (firstNonzeroEntry?_some_ne_zero A hentry)


structure LeadClearedState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) where
  t : TwoSidedTransform A
  pivot_ne_zero : t.B 0 0 ≠ 0
  pivot_normalized : t.B 0 0 = normalize (t.B 0 0)
  rowCleared : ∀ j : Fin n, t.B 0 j.succ = 0
  colCleared : ∀ i : Fin m, t.B i.succ 0 = 0


structure PivotDivisibleState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) where
  t : TwoSidedTransform A
  pivot_ne_zero : t.B 0 0 ≠ 0
  pivot_normalized : t.B 0 0 = normalize (t.B 0 0)
  rowCleared : ∀ j : Fin n, t.B 0 j.succ = 0
  colCleared : ∀ i : Fin m, t.B i.succ 0 = 0
  lowerRightDivisible : ∀ i : Fin m, ∀ j : Fin n, t.B 0 0 ∣ t.B i.succ j.succ


def PivotState.toLeadClearedState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : LeadClearedState A) :
    PivotState A :=
  { t := s.t
    pivot_ne_zero := s.pivot_ne_zero
    pivot_normalized := s.pivot_normalized }


def LeadClearedState.toPivotDivisibleState {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) : Ideal R :=
  Internal.pivotIdeal s.t.B


def LeadClearedState.pivotIdeal {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : LeadClearedState A) : Ideal R :=
  Internal.pivotIdeal s.t.B


def PivotDivisibleState.pivotIdeal {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotDivisibleState A) : Ideal R :=
  Internal.pivotIdeal s.t.B

/-!
The recursive Smith kernel has not landed yet. This subsection therefore keeps
the same-size layer factored into reusable pieces:

- a pure algebra kernel on `a b : R`
- HNF-to-Smith bridge lemmas for exact top-left gcd formulas
- row/column `prepareLead...` raw steps on `TwoSidedTransform`
- a single-step `improvePivot` wrapper and a strict-descent theorem

The next phase can then add the alternating/stabilization driver and outer
recursion without refactoring these proofs.
-/

def firstUndivisibleFirstCol? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) : Option (Fin m) :=
  firstUndivisible? (B 0 0) (fun i : Fin m => B i.succ 0)


def firstUndivisibleFirstRow? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) : Option (Fin n) :=
  firstUndivisible? (B 0 0) (fun j : Fin n => B 0 j.succ)


def prepareLeadColumnStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1)) : TwoSidedTransform A :=
  t.trans <|
    TwoSidedTransform.ofLeftTransform <|
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep i (LeftTransform.refl t.B)


def prepareLeadRowStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1)) : TwoSidedTransform A :=
  t.trans <|
    TwoSidedTransform.ofTransposeLeftTransform <|
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep j
        (LeftTransform.refl t.B.transpose)


theorem prepareLeadColumnStepData_topLeft_eq_normalize_gcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1)) (hwit : t.B i.succ 0 ≠ 0) :
    (prepareLeadColumnStepData t i).B 0 0 =
      normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
  simpa [prepareLeadColumnStepData] using
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_topLeft_eq_normalize_gcd i
      (LeftTransform.refl t.B) hwit


theorem prepareLeadColumnStepData_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1))
    (htop : t.B 0 0 ≠ 0) (hwit : t.B i.succ 0 ≠ 0) :
    (prepareLeadColumnStepData t i).B 0 0 ≠ 0 := by
  rw [prepareLeadColumnStepData_topLeft_eq_normalize_gcd t i hwit]
  intro hzero
  exact htop ((EuclideanDomain.gcd_eq_zero_iff.mp (normalize_eq_zero.mp hzero)).1)


theorem prepareLeadColumnStepData_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1)) (hwit : t.B i.succ 0 ≠ 0) :
    (prepareLeadColumnStepData t i).B 0 0 =
      normalize ((prepareLeadColumnStepData t i).B 0 0) := by
  rw [prepareLeadColumnStepData_topLeft_eq_normalize_gcd t i hwit]
  simpa using (normalize_idem (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0))).symm


theorem prepareLeadColumnStepData_preserves_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin (m + 1))
    (hprefix : ∀ j : Fin (m + 1), j.1 < i.1 -> t.B j.succ 0 = 0) :
    ∀ j : Fin (m + 1), j.1 < i.1.succ -> (prepareLeadColumnStepData t i).B j.succ 0 = 0 := by
  simpa [prepareLeadColumnStepData] using
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_prefix_zero i
      (LeftTransform.refl t.B) hprefix


theorem prepareLeadRowStepData_topLeft_eq_normalize_gcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1)) (hwit : t.B 0 j.succ ≠ 0) :
    (prepareLeadRowStepData t j).B 0 0 =
      normalize (EuclideanDomain.gcd (t.B 0 0) (t.B 0 j.succ)) := by
  simpa [prepareLeadRowStepData] using
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_topLeft_eq_normalize_gcd j
      (LeftTransform.refl t.B.transpose) hwit


theorem prepareLeadRowStepData_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1))
    (htop : t.B 0 0 ≠ 0) (hwit : t.B 0 j.succ ≠ 0) :
    (prepareLeadRowStepData t j).B 0 0 ≠ 0 := by
  rw [prepareLeadRowStepData_topLeft_eq_normalize_gcd t j hwit]
  intro hzero
  exact htop ((EuclideanDomain.gcd_eq_zero_iff.mp (normalize_eq_zero.mp hzero)).1)


theorem prepareLeadRowStepData_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1)) (hwit : t.B 0 j.succ ≠ 0) :
    (prepareLeadRowStepData t j).B 0 0 =
      normalize ((prepareLeadRowStepData t j).B 0 0) := by
  rw [prepareLeadRowStepData_topLeft_eq_normalize_gcd t j hwit]
  simpa using (normalize_idem (EuclideanDomain.gcd (t.B 0 0) (t.B 0 j.succ))).symm


theorem prepareLeadRowStepData_preserves_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 2)) R}
    (t : TwoSidedTransform A) (j : Fin (n + 1))
    (hprefix : ∀ c : Fin (n + 1), c.1 < j.1 -> t.B 0 c.succ = 0) :
    ∀ c : Fin (n + 1), c.1 < j.1.succ -> (prepareLeadRowStepData t j).B 0 c.succ = 0 := by
  have hprefixT :
      ∀ c : Fin (n + 1), c.1 < j.1 -> (LeftTransform.refl t.B.transpose).B c.succ 0 = 0 := by
    intro c hc
    simpa using hprefix c hc
  have hclear :=
    NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep_prefix_zero j
      (LeftTransform.refl t.B.transpose) hprefixT
  intro c hc
  simpa [prepareLeadRowStepData] using hclear c hc


def injectLowerRightWitnessToFirstColData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1)) : TwoSidedTransform A :=
  s.t.trans
    (TwoSidedTransform.addCols s.t.B j.succ 0 (1 : R) (by simpa using (Fin.succ_ne_zero j)))


theorem injectLowerRightWitnessToFirstCol_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (injectLowerRightWitnessToFirstColData s i j).B 0 0 = s.t.B 0 0 := by
  simp [injectLowerRightWitnessToFirstColData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, s.rowCleared j]


theorem injectLowerRightWitnessToFirstCol_target {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (injectLowerRightWitnessToFirstColData s i j).B i.succ 0 = s.t.B i.succ j.succ := by
  simp [injectLowerRightWitnessToFirstColData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, s.colCleared i]


def improvePivotStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1)) : TwoSidedTransform A :=
  prepareLeadColumnStepData (injectLowerRightWitnessToFirstColData s i j) i


theorem improvePivot_topLeft_eq_normalize_gcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 =
      normalize (EuclideanDomain.gcd (s.t.B 0 0) (s.t.B i.succ j.succ)) := by
  have hwit : (injectLowerRightWitnessToFirstColData s i j).B i.succ 0 ≠ 0 := by
    rw [injectLowerRightWitnessToFirstCol_target s i j]
    intro hzero
    exact hbad (hzero ▸ dvd_zero _)
  calc
    (improvePivotStepData s i j).B 0 0
        = normalize
            (EuclideanDomain.gcd
              ((injectLowerRightWitnessToFirstColData s i j).B 0 0)
              ((injectLowerRightWitnessToFirstColData s i j).B i.succ 0)) := by
              exact prepareLeadColumnStepData_topLeft_eq_normalize_gcd
                (injectLowerRightWitnessToFirstColData s i j) i hwit
    _ = normalize (EuclideanDomain.gcd (s.t.B 0 0) (s.t.B i.succ j.succ)) := by
          rw [injectLowerRightWitnessToFirstCol_topLeft s i j,
            injectLowerRightWitnessToFirstCol_target s i j]


theorem improvePivot_pivot_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 ≠ 0 := by
  rw [improvePivot_topLeft_eq_normalize_gcd s i j hbad]
  intro hzero
  exact s.pivot_ne_zero ((EuclideanDomain.gcd_eq_zero_iff.mp (normalize_eq_zero.mp hzero)).1)


theorem improvePivot_pivot_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 =
      normalize ((improvePivotStepData s i j).B 0 0) := by
  rw [improvePivot_topLeft_eq_normalize_gcd s i j hbad]
  simpa using (normalize_idem (EuclideanDomain.gcd (s.t.B 0 0) (s.t.B i.succ j.succ))).symm


theorem improvePivot_strict_descent {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    (improvePivotStepData s i j).B 0 0 ∣ s.t.B i.succ j.succ % s.t.B 0 0 ∧
      s.t.B i.succ j.succ % s.t.B 0 0 ≠ 0 ∧
      EuclideanDomain.r (s.t.B i.succ j.succ % s.t.B 0 0) (s.t.B 0 0) := by
  have hmodNe : s.t.B i.succ j.succ % s.t.B 0 0 ≠ 0 :=
    mod_ne_zero_of_not_dvd s.pivot_ne_zero hbad
  refine ⟨?_, hmodNe, EuclideanDomain.mod_lt _ s.pivot_ne_zero⟩
  rw [improvePivot_topLeft_eq_normalize_gcd s i j hbad]
  exact (normalize_dvd_iff).2 (gcd_dvd_mod (a := s.t.B 0 0) (b := s.t.B i.succ j.succ))


def improvePivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 2)) R}
    (s : LeadClearedState A) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hbad : ¬ s.t.B 0 0 ∣ s.t.B i.succ j.succ) :
    PivotState A :=
  { t := improvePivotStepData s i j
    pivot_ne_zero := improvePivot_pivot_ne_zero s i j hbad
    pivot_normalized := improvePivot_pivot_normalized s i j hbad }


private def clearFirstColumnCoeff {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin m) : R :=
  -(B i.succ 0 / B 0 0)


private def clearFirstRowCoeff {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    (B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (j : Fin n) : R :=
  -(B 0 j.succ / B 0 0)


private def clearFirstColumnByPivotStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin m) : TwoSidedTransform A :=
  t.trans
    (TwoSidedTransform.addRows t.B 0 i.succ (clearFirstColumnCoeff t.B i)
      (by simpa [eq_comm] using (Fin.succ_ne_zero i)))


private def clearFirstRowByPivotStepData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j : Fin n) : TwoSidedTransform A :=
  t.trans
    (TwoSidedTransform.addCols t.B 0 j.succ (clearFirstRowCoeff t.B j)
      (by simpa [eq_comm] using (Fin.succ_ne_zero j)))


private def clearFirstColumnByPivotTransform {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) : TwoSidedTransform A :=
  clearFirstColumnByPivotStepData s.t i


private def clearFirstRowByPivotTransform {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) : TwoSidedTransform A :=
  clearFirstRowByPivotStepData s.t j


@[simp] theorem clearFirstColumnByPivotTransform_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) :
    (clearFirstColumnByPivotTransform s i).B 0 0 = s.t.B 0 0 := by
  have hne : (0 : Fin (m + 1)) ≠ i.succ := by
    simpa [eq_comm] using (Fin.succ_ne_zero i)
  change (clearFirstColumnByPivotStepData s.t i).B 0 0 = s.t.B 0 0
  simp [clearFirstColumnByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addRows,
    applyRowOperation, hne]


@[simp] theorem clearFirstRowByPivotTransform_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) :
    (clearFirstRowByPivotTransform s j).B 0 0 = s.t.B 0 0 := by
  have hne : (0 : Fin (n + 1)) ≠ j.succ := by
    simpa [eq_comm] using (Fin.succ_ne_zero j)
  change (clearFirstRowByPivotStepData s.t j).B 0 0 = s.t.B 0 0
  simp [clearFirstRowByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, hne]


def clearFirstColumnByPivotStep {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m)
    (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n)
    (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (clearFirstColumnByPivotStep s i hdiv).t.B 0 0 = s.t.B 0 0 := by
  change (clearFirstColumnByPivotTransform s i).B 0 0 = s.t.B 0 0
  simp


theorem clearFirstColumnByPivotStep_topRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) (j : Fin (n + 1)) :
    (clearFirstColumnByPivotStep s i hdiv).t.B 0 j = s.t.B 0 j := by
  have hne : (0 : Fin (m + 1)) ≠ i.succ := by
    simpa [eq_comm] using (Fin.succ_ne_zero i)
  change (clearFirstColumnByPivotStepData s.t i).B 0 j = s.t.B 0 j
  simp [clearFirstColumnByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addRows,
    applyRowOperation, hne]


theorem clearFirstColumnByPivotStep_otherRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
    (clearFirstColumnByPivotStep s i hdiv).t.B i.succ 0 = 0 := by
  have hmul :
      (s.t.B i.succ 0 / s.t.B 0 0) * s.t.B 0 0 = s.t.B i.succ 0 := by
    rw [mul_comm]
    exact EuclideanDomain.mul_div_cancel' s.pivot_ne_zero hdiv
  calc
    (clearFirstColumnByPivotStep s i hdiv).t.B i.succ 0
        = s.t.B i.succ 0 + (-(s.t.B i.succ 0 / s.t.B 0 0)) * s.t.B 0 0 := by
            change (clearFirstColumnByPivotStepData s.t i).B i.succ 0 =
              s.t.B i.succ 0 + (-(s.t.B i.succ 0 / s.t.B 0 0)) * s.t.B 0 0
            simp [clearFirstColumnByPivotStepData, TwoSidedTransform.trans,
              TwoSidedTransform.addRows, clearFirstColumnCoeff, applyRowOperation]
    _ = s.t.B i.succ 0 - (s.t.B i.succ 0 / s.t.B 0 0) * s.t.B 0 0 := by
          ring
    _ = 0 := by rw [hmul]; ring


theorem clearFirstColumnByPivotStep_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (clearFirstRowByPivotStep s j hdiv).t.B 0 0 = s.t.B 0 0 := by
  change (clearFirstRowByPivotTransform s j).B 0 0 = s.t.B 0 0
  simp


theorem clearFirstRowByPivotStep_firstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) (i : Fin (m + 1)) :
    (clearFirstRowByPivotStep s j hdiv).t.B i 0 = s.t.B i 0 := by
  have hne : (0 : Fin (n + 1)) ≠ j.succ := by
    simpa [eq_comm] using (Fin.succ_ne_zero j)
  change (clearFirstRowByPivotStepData s.t j).B i 0 = s.t.B i 0
  simp [clearFirstRowByPivotStepData, TwoSidedTransform.trans, TwoSidedTransform.addCols,
    applyColumnOperation, hne]


theorem clearFirstRowByPivotStep_otherCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    (clearFirstRowByPivotStep s j hdiv).t.B 0 j.succ = 0 := by
  have hmul :
      s.t.B 0 0 * (s.t.B 0 j.succ / s.t.B 0 0) = s.t.B 0 j.succ := by
    exact EuclideanDomain.mul_div_cancel' s.pivot_ne_zero hdiv
  calc
    (clearFirstRowByPivotStep s j hdiv).t.B 0 j.succ
        = s.t.B 0 j.succ + (-(s.t.B 0 j.succ / s.t.B 0 0)) * s.t.B 0 0 := by
            change (clearFirstRowByPivotStepData s.t j).B 0 j.succ =
              s.t.B 0 j.succ + (-(s.t.B 0 j.succ / s.t.B 0 0)) * s.t.B 0 0
            simp [clearFirstRowByPivotStepData, TwoSidedTransform.trans,
              TwoSidedTransform.addCols, clearFirstRowCoeff, applyColumnOperation]
    _ = s.t.B 0 j.succ - (s.t.B 0 j.succ / s.t.B 0 0) * s.t.B 0 0 := by
          ring
    _ = 0 := by
          rw [show (s.t.B 0 j.succ / s.t.B 0 0) * s.t.B 0 0 = s.t.B 0 j.succ by
            simpa [mul_comm] using hmul]
          ring


theorem clearFirstRowByPivotStep_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (i : Fin m) (hdiv : s.t.B 0 0 ∣ s.t.B i.succ 0) :
    clearFirstColumnByPivotStepData s.t i = (clearFirstColumnByPivotStep s i hdiv).t :=
  rfl


theorem clearFirstRowByPivotStepData_eq {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (s : PivotState A) (j : Fin n) (hdiv : s.t.B 0 0 ∣ s.t.B 0 j.succ) :
    clearFirstRowByPivotStepData s.t j = (clearFirstRowByPivotStep s j hdiv).t :=
  rfl


private theorem clearFirstColumnByPivotStepData_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (i : Fin m)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B i.succ 0) :
    (clearFirstColumnByPivotStepData t i).B 0 0 = t.B 0 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstColumnByPivotTransform s i).B 0 0 = s.t.B 0 0
  exact clearFirstColumnByPivotTransform_topLeft s i


private theorem clearFirstColumnByPivotStepData_topRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstColumnByPivotStepData_eq] using
    clearFirstColumnByPivotStep_topRow s i hdiv j


private theorem clearFirstColumnByPivotStepData_otherRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstColumnByPivotStepData_eq] using
    clearFirstColumnByPivotStep_otherRow s i r hdiv hri


private theorem clearFirstColumnByPivotStepData_target_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstColumnByPivotStepData_eq] using
    clearFirstColumnByPivotStep_target_zero s i hdiv


private theorem clearFirstColumnByPivotStepData_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstColumnByPivotStepData_eq] using
    clearFirstColumnByPivotStep_prefix_zero s i hdiv hprefix


private theorem clearFirstRowByPivotStepData_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (t : TwoSidedTransform A) (j : Fin n)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : t.B 0 0 ∣ t.B 0 j.succ) :
    (clearFirstRowByPivotStepData t j).B 0 0 = t.B 0 0 := by
  let s : PivotState A :=
    { t := t
      pivot_ne_zero := htop
      pivot_normalized := hnorm }
  change (clearFirstRowByPivotTransform s j).B 0 0 = s.t.B 0 0
  exact clearFirstRowByPivotTransform_topLeft s j


private theorem clearFirstRowByPivotStepData_firstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstRowByPivotStepData_eq] using
    clearFirstRowByPivotStep_firstCol s j hdiv i


private theorem clearFirstRowByPivotStepData_otherCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstRowByPivotStepData_eq] using
    clearFirstRowByPivotStep_otherCol s j c hdiv hcj i


private theorem clearFirstRowByPivotStepData_target_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstRowByPivotStepData_eq] using
    clearFirstRowByPivotStep_target_zero s j hdiv


private theorem clearFirstRowByPivotStepData_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
  simpa [s, clearFirstRowByPivotStepData_eq] using
    clearFirstRowByPivotStep_prefix_zero s j hdiv hprefix


def clearFirstColumnByPivotLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ m -> TwoSidedTransform A -> TwoSidedTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnByPivotLoop k hk' t
      let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      clearFirstColumnByPivotStepData t' i


def clearFirstRowByPivotLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ n -> TwoSidedTransform A -> TwoSidedTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let hk' : k ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstRowByPivotLoop k hk' t
      let j : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      clearFirstRowByPivotStepData t' j


private theorem clearFirstColumnByPivotLoop_topLeft_colDivisible {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ i : Fin m, t.B 0 0 ∣ t.B i.succ 0) :
    (clearFirstColumnByPivotLoop k hk t).B 0 0 = t.B 0 0 :=
  (clearFirstColumnByPivotLoop_topLeft_colDivisible k hk t htop hnorm hdiv).1


theorem clearFirstColumnByPivotLoop_colDivisible {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ i : Fin m, t.B 0 0 ∣ t.B i.succ 0) :
    ∀ i : Fin m, (clearFirstColumnByPivotLoop k hk t).B 0 0 ∣
      (clearFirstColumnByPivotLoop k hk t).B i.succ 0 :=
  (clearFirstColumnByPivotLoop_topLeft_colDivisible k hk t htop hnorm hdiv).2


theorem clearFirstRowByPivotLoop_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ n) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ j : Fin n, t.B 0 0 ∣ t.B 0 j.succ) :
    (clearFirstRowByPivotLoop k hk t).B 0 0 = t.B 0 0 :=
  (clearFirstRowByPivotLoop_topLeft_rowDivisible k hk t htop hnorm hdiv).1


theorem clearFirstRowByPivotLoop_rowDivisible {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ n) (t : TwoSidedTransform A)
    (htop : t.B 0 0 ≠ 0)
    (hnorm : t.B 0 0 = normalize (t.B 0 0))
    (hdiv : ∀ j : Fin n, t.B 0 0 ∣ t.B 0 j.succ) :
    ∀ j : Fin n, (clearFirstRowByPivotLoop k hk t).B 0 0 ∣
      (clearFirstRowByPivotLoop k hk t).B 0 j.succ :=
  (clearFirstRowByPivotLoop_topLeft_rowDivisible k hk t htop hnorm hdiv).2


theorem clearFirstColumnByPivotLoop_topRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
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


end Internal


/-- Public result package for a two-sided Smith normal form transform. -/
structure SNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  S : _root_.Matrix m n R
  V : _root_.Matrix n n R
  two_sided_mul : U * A * V = S
  isSmith : IsSmithNormalForm S

noncomputable def SNFResult.invariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) : List R :=
  smithInvariantFactors result.S

/-- Package an existing two-sided certificate together with a Smith witness.

This is the intended public constructor when an external proof or example has
already produced a concrete two-sided certificate and a separate Smith witness.
It keeps the public result API lightweight without forcing users to build the
internal Smith recursion infrastructure.
-/
def SNFResult.ofCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R}
    (cert : NormalForms.Matrix.Certificates.TwoSidedCertificate A)
    (hSmith : IsSmithNormalForm cert.result) :
    SNFResult A :=
  { U := cert.U
    S := cert.result
    V := cert.V
    two_sided_mul := cert.equation
    isSmith := hSmith }


/-- Forget the Smith witness and keep only the two-sided transformation data. -/
def SNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    NormalForms.Matrix.Certificates.TwoSidedCertificate A :=
  { U := result.U
    result := result.S
    V := result.V
    equation := result.two_sided_mul }


/-- Executable Smith-normal-form entrypoint. -/
noncomputable def smithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [CanonicalMod R]
    (A : _root_.Matrix m n R) : Option (SNFResult A) :=
  none


theorem smithNormalForm_isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : SNFResult A}
    (_hresult : smithNormalForm A = some result) :
    IsSmithNormalForm result.S := by
  exact result.isSmith

end NormalForms.Matrix.Smith
