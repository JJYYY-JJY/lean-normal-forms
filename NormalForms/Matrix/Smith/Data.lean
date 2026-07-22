/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Matrix.Smith.Uniqueness
import all NormalForms.Matrix.Smith.Uniqueness

/-!
# Intrinsic Smith Data

The canonical diagonal data attached to a Smith-normal-form matrix.  This
interface deliberately forgets transformation matrices and execution traces:
it stores the complete normalized diagonal, including its zero tail and unit
entries, together with the exact nonzero-prefix rank.
-/

namespace NormalForms.Matrix.Smith

/--
The ordered canonical data of an `m × n` Smith-normal-form matrix.

`diagonal` contains all `min m n` diagonal entries.  The first `rank` entries
are nonzero and the remaining entries are zero; unit entries are retained.
-/
public structure SmithData (m n : Nat) (R : Type u)
    [EuclideanDomain R] [NormalizationMonoid R] where
  rank : Nat
  rank_le : rank ≤ Nat.min m n
  diagonal : Fin (Nat.min m n) → R
  nonzero_prefix : ∀ i, i.1 < rank → diagonal i ≠ 0
  zero_tail : ∀ i, rank ≤ i.1 → diagonal i = 0
  normalized : ∀ i, diagonal i = normalize (diagonal i)
  divisibility : ∀ i j, i.1 ≤ j.1 → diagonal i ∣ diagonal j

@[ext] public theorem SmithData.ext {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {left right : SmithData m n R}
    (rank : left.rank = right.rank)
    (diagonal : left.diagonal = right.diagonal) :
    left = right := by
  cases left
  cases right
  cases rank
  cases diagonal
  rfl

/-- The complete diagonal of a matrix at the canonical `Fin` indexing seam. -/
@[expose] public def smithDiagonalFin {m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin m) (Fin n) R) :
    Fin (Nat.min m n) → R :=
  fun i =>
    A (Fin.castLE (Nat.min_le_left m n) i)
      (Fin.castLE (Nat.min_le_right m n) i)

namespace SmithData

theorem smithDiagonalFin_eq_diagEntry {m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin m) (Fin n) R) (i : Fin (Nat.min m n)) :
    smithDiagonalFin A i = Internal.diagEntry A i.1 i.2 := by
  rfl

/--
Extract intrinsic data from a canonical Smith matrix.  The rank is the exact
length of the nonzero invariant-factor prefix.
-/
@[expose] public noncomputable def ofSmithMatrix {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (hA : IsSmithNormalFormFin A) :
    SmithData m n R where
  rank := (smithInvariantFactorsFin A).length
  rank_le := by
    exact Internal.invariantFactors_length_le_min A
  diagonal := smithDiagonalFin A
  nonzero_prefix := by
    intro i hi
    rw [smithDiagonalFin_eq_diagEntry]
    exact
      Internal.diagEntry_ne_zero_of_lt_invariantFactors_length hA
        i.1 hi i.2
  zero_tail := by
    intro i hi
    rw [smithDiagonalFin_eq_diagEntry]
    exact
      Internal.diagEntry_eq_zero_of_invariantFactors_length_le hA
        i.1 hi i.2
  normalized := by
    intro i
    rw [smithDiagonalFin_eq_diagEntry]
    exact (Internal.isSmithNormalFormFin_toDiag hA).2.1 i.1 i.2
  divisibility := by
    intro i j hij
    rw [smithDiagonalFin_eq_diagEntry, smithDiagonalFin_eq_diagEntry]
    exact
      Internal.diagEntry_dvd_of_diagChain
        (Internal.isSmithNormalFormFin_toDiag hA).2.2
        i.1 j.1 hij i.2 j.2

@[simp] public theorem ofSmithMatrix_rank {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (hA : IsSmithNormalFormFin A) :
    (ofSmithMatrix A hA).rank = (smithInvariantFactorsFin A).length :=
  rfl

@[simp] public theorem ofSmithMatrix_diagonal {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (hA : IsSmithNormalFormFin A) (i : Fin (Nat.min m n)) :
    (ofSmithMatrix A hA).diagonal i = smithDiagonalFin A i :=
  rfl

end SmithData

/-- Intrinsic Smith data carried by a strong canonical `Fin` result. -/
@[expose] public noncomputable def SNFResultFin.smithData {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (result : SNFResultFin A) :
    SmithData m n R :=
  SmithData.ofSmithMatrix result.S result.isSmith

@[simp] public theorem SNFResultFin.smithData_rank {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (result : SNFResultFin A) :
    result.smithData.rank = (smithInvariantFactorsFin result.S).length :=
  rfl

@[simp] public theorem SNFResultFin.smithData_diagonal {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (result : SNFResultFin A) (i : Fin (Nat.min m n)) :
    result.smithData.diagonal i = smithDiagonalFin result.S i :=
  rfl

/--
Intrinsic Smith data for an arbitrary finite indexing.  It is derived solely
from the stored canonical `Fin` result, so no original-index copy can drift.
-/
@[expose] public noncomputable def SNFResult.smithData {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    SmithData (Fintype.card m) (Fintype.card n) R :=
  result.finResult.smithData

@[simp] public theorem SNFResult.smithData_rank {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    result.smithData.rank = result.invariantFactors.length := by
  rw [result.invariantFactors_eq_fin]
  rfl

@[simp] public theorem SNFResult.smithData_diagonal {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A)
    (i : Fin (Nat.min (Fintype.card m) (Fintype.card n))) :
    result.smithData.diagonal i = smithDiagonalFin result.finResult.S i :=
  rfl

/-- Changing the stored finite indexing does not change intrinsic Smith data. -/
public theorem SNFResult.smithData_eq_of_indexing_change {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (source target : SNFResult A) :
    source.smithData = target.smithData := by
  apply SmithData.ext
  · change
      (smithInvariantFactorsFin source.finResult.S).length =
        (smithInvariantFactorsFin target.finResult.S).length
    rw [source.finResult_S_eq target]
  · funext i
    change
      smithDiagonalFin source.finResult.S i =
        smithDiagonalFin target.finResult.S i
    rw [source.finResult_S_eq target]

end NormalForms.Matrix.Smith
