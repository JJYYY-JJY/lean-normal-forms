/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import NormalForms.Basic

/-!
# Explicit finite matrix indexing

Normal-form semantics depend on an ordering of finite row and column types.
This module makes that choice data rather than hiding `Fintype.equivFin`.
-/

namespace NormalForms.Matrix

/-- An explicit enumeration of a finite type by its cardinality. -/
public structure FiniteIndexing (α : Type _) [Fintype α] where
  equiv : α ≃ Fin (Fintype.card α)

namespace FiniteIndexing

/-- The identity enumeration of `Fin n`. -/
@[expose] public def fin (n : Nat) : FiniteIndexing (Fin n) :=
  ⟨finCongr (Fintype.card_fin n).symm⟩

/-- Package a caller-supplied enumeration. -/
@[expose] public def ofEquiv {α : Type _} [Fintype α]
    (e : α ≃ Fin (Fintype.card α)) : FiniteIndexing α :=
  ⟨e⟩

/-- Enumerate a finite linear order in strictly increasing order. -/
@[expose] public def ordered (α : Type _) [Fintype α] [LinearOrder α] :
    FiniteIndexing α :=
  ⟨(Fintype.orderIsoFinOfCardEq α rfl).symm.toEquiv⟩

/-- Choose an arbitrary enumeration when the caller does not care about order. -/
public noncomputable def arbitrary (α : Type _) [Fintype α] :
    FiniteIndexing α :=
  ⟨Fintype.equivFin α⟩

end FiniteIndexing

/-- Explicit row and column enumerations for a finite matrix. -/
public structure MatrixIndexing (m n : Type _) [Fintype m] [Fintype n] where
  rows : FiniteIndexing m
  cols : FiniteIndexing n

namespace MatrixIndexing

/-- Canonical identity indexing for a `Fin` matrix. -/
@[expose] public def fin (m n : Nat) : MatrixIndexing (Fin m) (Fin n) :=
  ⟨FiniteIndexing.fin m, FiniteIndexing.fin n⟩

/-- Package caller-supplied row and column equivalences. -/
@[expose] public def ofEquiv {m n : Type _} [Fintype m] [Fintype n]
    (rows : m ≃ Fin (Fintype.card m)) (cols : n ≃ Fin (Fintype.card n)) :
    MatrixIndexing m n :=
  ⟨FiniteIndexing.ofEquiv rows, FiniteIndexing.ofEquiv cols⟩

/-- Increasing enumeration on both finite linear orders. -/
@[expose] public def ordered (m n : Type _) [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] : MatrixIndexing m n :=
  ⟨FiniteIndexing.ordered m, FiniteIndexing.ordered n⟩

/-- Arbitrary row and column enumerations. -/
public noncomputable def arbitrary (m n : Type _) [Fintype m] [Fintype n] :
    MatrixIndexing m n :=
  ⟨FiniteIndexing.arbitrary m, FiniteIndexing.arbitrary n⟩

/-- Reindex a matrix according to an explicit indexing choice. -/
@[expose] public def reindex {m n R : Type _} [Fintype m] [Fintype n]
    (indexing : MatrixIndexing m n) (A : _root_.Matrix m n R) :
    _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) R :=
  _root_.Matrix.reindex indexing.rows.equiv indexing.cols.equiv A

/-- Row permutation carrying a matrix from `source` enumeration to `target`. -/
@[expose] public def rowPermutation {m n R : Type _}
  [Fintype m] [Fintype n] [Zero R] [One R]
    (source target : MatrixIndexing m n) :
    _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) R :=
  Equiv.Perm.permMatrix R
    (target.rows.equiv.symm.trans source.rows.equiv :
      Equiv.Perm (Fin (Fintype.card m)))

/-- Column permutation carrying a matrix from `source` enumeration to `target`. -/
@[expose] public def columnPermutation {m n R : Type _}
  [Fintype m] [Fintype n] [Zero R] [One R]
    (source target : MatrixIndexing m n) :
    _root_.Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) R :=
  Equiv.Perm.permMatrix R
    (source.cols.equiv.symm.trans target.cols.equiv :
      Equiv.Perm (Fin (Fintype.card n)))

/-- Two explicit indexings of one matrix differ by concrete permutation matrices. -/
public theorem rowPermutation_mul_reindex_mul_columnPermutation
    {m n R : Type _} [Fintype m] [Fintype n] [Semiring R]
    (source target : MatrixIndexing m n) (A : _root_.Matrix m n R) :
    source.rowPermutation (R := R) target * source.reindex A *
        source.columnPermutation (R := R) target =
      target.reindex A := by
  change
    (target.rows.equiv.symm.trans source.rows.equiv).toPEquiv.toMatrix *
          source.reindex A *
        (source.cols.equiv.symm.trans target.cols.equiv).toPEquiv.toMatrix =
      target.reindex A
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [reindex]

/-- Reversing an indexing change is a left inverse on row permutations. -/
public theorem rowPermutation_reverse_mul {m n R : Type _}
    [Fintype m] [Fintype n] [Semiring R]
    (source target : MatrixIndexing m n) :
    target.rowPermutation (R := R) source *
        source.rowPermutation (R := R) target =
      (1 : _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) R) := by
  change
    (source.rows.equiv.symm.trans target.rows.equiv).toPEquiv.toMatrix *
        (target.rows.equiv.symm.trans source.rows.equiv).toPEquiv.toMatrix = 1
  rw [← PEquiv.toMatrix_trans]
  have h :
      (source.rows.equiv.symm.trans target.rows.equiv).toPEquiv.trans
          (target.rows.equiv.symm.trans source.rows.equiv).toPEquiv =
        PEquiv.refl _ := by
    have he :
        (source.rows.equiv.symm.trans target.rows.equiv).trans
            (target.rows.equiv.symm.trans source.rows.equiv) =
          Equiv.refl _ := by
      ext i
      simp
    simpa [Equiv.toPEquiv_trans] using congrArg Equiv.toPEquiv he
  rw [h]
  exact PEquiv.toMatrix_refl

/-- Reversing an indexing change is a right inverse on row permutations. -/
public theorem rowPermutation_mul_reverse {m n R : Type _}
    [Fintype m] [Fintype n] [Semiring R]
    (source target : MatrixIndexing m n) :
    source.rowPermutation (R := R) target *
        target.rowPermutation (R := R) source =
      (1 : _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) R) := by
  simpa using rowPermutation_reverse_mul (R := R) target source

/-- Reversing an indexing change is a left inverse on column permutations. -/
public theorem columnPermutation_reverse_mul {m n R : Type _}
    [Fintype m] [Fintype n] [Semiring R]
    (source target : MatrixIndexing m n) :
    target.columnPermutation (R := R) source *
        source.columnPermutation (R := R) target =
      (1 : _root_.Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) R) := by
  change
    (target.cols.equiv.symm.trans source.cols.equiv).toPEquiv.toMatrix *
        (source.cols.equiv.symm.trans target.cols.equiv).toPEquiv.toMatrix = 1
  rw [← PEquiv.toMatrix_trans]
  have h :
      (target.cols.equiv.symm.trans source.cols.equiv).toPEquiv.trans
          (source.cols.equiv.symm.trans target.cols.equiv).toPEquiv =
        PEquiv.refl _ := by
    have he :
        (target.cols.equiv.symm.trans source.cols.equiv).trans
            (source.cols.equiv.symm.trans target.cols.equiv) =
          Equiv.refl _ := by
      ext i
      simp
    simpa [Equiv.toPEquiv_trans] using congrArg Equiv.toPEquiv he
  rw [h]
  exact PEquiv.toMatrix_refl

/-- Reversing an indexing change is a right inverse on column permutations. -/
public theorem columnPermutation_mul_reverse {m n R : Type _}
    [Fintype m] [Fintype n] [Semiring R]
    (source target : MatrixIndexing m n) :
    source.columnPermutation (R := R) target *
        target.columnPermutation (R := R) source =
      (1 : _root_.Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) R) := by
  simpa using columnPermutation_reverse_mul (R := R) target source

end MatrixIndexing

end NormalForms.Matrix
