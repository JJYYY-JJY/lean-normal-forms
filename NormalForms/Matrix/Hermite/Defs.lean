import Mathlib.Data.Int.ModEq
import NormalForms.Matrix.Certificates

/-!
# Hermite Normal Form Definitions

Core Hermite predicates, canonical remainder assumptions, and lightweight search lemmas.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates

/-- A Euclidean domain whose remainder choice is canonical, so `%` is idempotent. -/
class CanonicalMod (R : Type _) [EuclideanDomain R] : Prop where
  mod_mod : ∀ a b : R, (a % b) % b = a % b
  reduced_eq_of_dvd_sub :
    ∀ {a b m : R}, a = a % m -> b = b % m -> m ∣ b - a -> a = b

instance : CanonicalMod Int where
  mod_mod := Int.emod_emod
  reduced_eq_of_dvd_sub := by
    intro a b m ha hb hdiv
    have hmod : a % m = b % m := by
      simpa using Int.ModEq.eq ((Int.modEq_iff_dvd).2 hdiv)
    calc
      a = a % m := ha
      _ = b % m := hmod
      _ = b := hb.symm

instance : CanonicalMod (Polynomial Rat) where
  mod_mod := by
    intro a b
    by_cases hb : b = 0
    · simp [hb]
    · exact (Polynomial.mod_eq_self_iff hb).2 (Polynomial.degree_mod_lt a hb)
  reduced_eq_of_dvd_sub := by
    intro a b m ha hb hdiv
    have hmod : b % m = a % m := Polynomial.mod_eq_of_dvd_sub hdiv
    calc
      a = a % m := ha
      _ = b % m := hmod.symm
      _ = b := hb.symm


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
                have hEq : j'.succ = j.succ := by
                  simpa [htail] using hsome
                have hEq' : j' = j := by
                  apply Fin.ext
                  exact Nat.succ.inj (congrArg Fin.val hEq)
                subst hEq'
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
                    have hk : k.succ = i'.succ := by
                      simpa [htail] using hsome
                    have hk' : k = i' := by
                      apply Fin.ext
                      exact Nat.succ.inj (congrArg Fin.val hk)
                    subst hk'
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



end NormalForms.Matrix.Hermite
