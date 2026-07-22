/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Result
import all Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Lifting a prefix row transform

The total LLL wrapper reduces only the independent row prefix.  This module
embeds its transform as a block diagonal matrix and transports the result back
to the original `Fin` row indexing.
-/

namespace NormalForms.Research.LLL.Internal.PrefixLift

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Research.LLL

/-- Split `Fin rows` into a leading prefix and its arithmetic complement. -/
public def prefixEquiv {rank rows : Nat} (rank_le : rank ≤ rows) :
    Fin rank ⊕ Fin (rows - rank) ≃ Fin rows :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le rank_le))

@[simp] private theorem prefixEquiv_inl {rank rows : Nat} (rank_le : rank ≤ rows)
    (row : Fin rank) :
    prefixEquiv rank_le (Sum.inl row) = Fin.castLE rank_le row := by
  ext
  rfl

private def blockTransform {rank rows : Nat}
    (transform : Matrix (Fin rank) (Fin rank) Int) :
    Matrix (Fin rank ⊕ Fin (rows - rank)) (Fin rank ⊕ Fin (rows - rank)) Int :=
  Matrix.fromBlocks transform 0 0 1

/-- Embed a prefix transform with identity on all remaining rows. -/
public def liftPrefixTransform {rank rows : Nat} (rank_le : rank ≤ rows)
    (transform : Matrix (Fin rank) (Fin rank) Int) :
    Matrix (Fin rows) (Fin rows) Int :=
  Matrix.reindex (prefixEquiv rank_le) (prefixEquiv rank_le)
    (blockTransform (rows := rows) transform)

private theorem blockTransform_mul {rank rows : Nat}
    (left right : Matrix (Fin rank) (Fin rank) Int) :
    blockTransform (rows := rows) left * blockTransform (rows := rows) right =
      blockTransform (rows := rows) (left * right) := by
  simp [blockTransform, Matrix.fromBlocks_multiply]

@[simp] private theorem blockTransform_one {rank rows : Nat} :
    blockTransform (rows := rows) (1 : Matrix (Fin rank) (Fin rank) Int) = 1 := by
  exact Matrix.fromBlocks_one

@[simp] public theorem liftPrefixTransform_one {rank rows : Nat}
    (rank_le : rank ≤ rows) :
    liftPrefixTransform rank_le (1 : Matrix (Fin rank) (Fin rank) Int) = 1 := by
  simp [liftPrefixTransform, blockTransform_one]

public theorem liftPrefixTransform_mul {rank rows : Nat}
    (rank_le : rank ≤ rows)
    (left right : Matrix (Fin rank) (Fin rank) Int) :
    liftPrefixTransform rank_le left * liftPrefixTransform rank_le right =
      liftPrefixTransform rank_le (left * right) := by
  simp [liftPrefixTransform, blockTransform_mul]

/-- Explicit inverse certificate for the lifted prefix transform. -/
public def liftPrefixCertificate {rank rows : Nat} (rank_le : rank ≤ rows)
    {transform : Matrix (Fin rank) (Fin rank) Int}
    (certificate : MatrixInverseCertificate transform) :
    MatrixInverseCertificate (liftPrefixTransform rank_le transform) := by
  let blockCertificate : MatrixInverseCertificate
      (blockTransform (rows := rows) transform) :=
    { inverse := blockTransform (rows := rows) certificate.inverse
      left_inv := by
        rw [blockTransform_mul, certificate.left_inv, blockTransform_one]
      right_inv := by
        rw [blockTransform_mul, certificate.right_inv, blockTransform_one] }
  exact blockCertificate.reindex (prefixEquiv rank_le)

private def prefixWithZero {rank rows columns : Nat}
    (basis : Matrix (Fin rank) (Fin columns) Int) :
    Matrix (Fin rank ⊕ Fin (rows - rank)) (Fin columns) Int :=
  Sum.elim basis (fun _ _ => 0)

/-- Extend a prefix matrix by literal zero rows. -/
public def extendPrefixWithZeros {rank rows columns : Nat} (rank_le : rank ≤ rows)
    (basis : Matrix (Fin rank) (Fin columns) Int) :
    Matrix (Fin rows) (Fin columns) Int :=
  Matrix.reindex (prefixEquiv rank_le) (Equiv.refl _) <|
    prefixWithZero (rows := rows) basis

private theorem blockTransform_mul_prefixWithZero {rank rows columns : Nat}
    (transform : Matrix (Fin rank) (Fin rank) Int)
    (basis : Matrix (Fin rank) (Fin columns) Int) :
    blockTransform (rows := rows) transform * prefixWithZero (rows := rows) basis =
      prefixWithZero (rows := rows) (transform * basis) := by
  ext row column
  cases row with
  | inl row =>
      simp [blockTransform, prefixWithZero, Matrix.mul_apply,
        Fintype.sum_sum_type]
  | inr row =>
      simp [blockTransform, prefixWithZero, Matrix.mul_apply,
        Fintype.sum_sum_type]

private def splitRows {rank rows columns : Nat} (rank_le : rank ≤ rows)
    (basis : Matrix (Fin rows) (Fin columns) Int) :
    Matrix (Fin rank ⊕ Fin (rows - rank)) (Fin columns) Int :=
  Matrix.reindex (prefixEquiv rank_le).symm (Equiv.refl _) basis

private theorem splitRows_eq_prefixWithZero {rank rows columns : Nat}
    (rank_le : rank ≤ rows) (basis : Matrix (Fin rows) (Fin columns) Int)
    (zeroTail : ∀ row : Fin rows, rank ≤ row.val → basis row = 0) :
    splitRows rank_le basis =
      prefixWithZero (rows := rows) (rowPrefix rank_le basis) := by
  ext row column
  cases row with
  | inl row =>
      simp [splitRows, prefixWithZero, rowPrefix, prefixEquiv_inl]
  | inr row =>
      have afterRank : rank ≤ (prefixEquiv rank_le (Sum.inr row)).val := by
        simp [prefixEquiv]
      have zero := congrFun (zeroTail (prefixEquiv rank_le (Sum.inr row)) afterRank) column
      simpa [splitRows, prefixWithZero] using zero

/-- Multiplying a zero-tailed matrix by the lifted transform reduces exactly its prefix. -/
public theorem liftPrefixTransform_mul_of_zeroTail {rank rows columns : Nat}
    (rank_le : rank ≤ rows)
    (transform : Matrix (Fin rank) (Fin rank) Int)
    (basis : Matrix (Fin rows) (Fin columns) Int)
    (zeroTail : ∀ row : Fin rows, rank ≤ row.val → basis row = 0) :
    liftPrefixTransform rank_le transform * basis =
      extendPrefixWithZeros rank_le (transform * rowPrefix rank_le basis) := by
  have unsplit : Matrix.reindex (prefixEquiv rank_le) (Equiv.refl _)
      (splitRows rank_le basis) = basis := by
    simp [splitRows]
  have reindexProduct := Matrix.reindexLinearEquiv_mul Int Int
    (prefixEquiv rank_le) (prefixEquiv rank_le) (Equiv.refl _)
    (blockTransform (rows := rows) transform) (splitRows rank_le basis)
  calc
    liftPrefixTransform rank_le transform * basis =
        liftPrefixTransform rank_le transform *
          Matrix.reindex (prefixEquiv rank_le) (Equiv.refl _)
            (splitRows rank_le basis) := by rw [unsplit]
    _ = Matrix.reindex (prefixEquiv rank_le) (Equiv.refl _)
          (blockTransform (rows := rows) transform * splitRows rank_le basis) := by
      simp [liftPrefixTransform]
    _ = extendPrefixWithZeros rank_le (transform * rowPrefix rank_le basis) := by
      rw [splitRows_eq_prefixWithZero rank_le basis zeroTail,
        blockTransform_mul_prefixWithZero]
      rfl

@[simp] public theorem rowPrefix_extendPrefixWithZeros {rank rows columns : Nat}
    (rank_le : rank ≤ rows) (basis : Matrix (Fin rank) (Fin columns) Int) :
    rowPrefix rank_le (extendPrefixWithZeros rank_le basis) = basis := by
  ext row column
  have inverseEquation :
      (prefixEquiv rank_le).symm (Fin.castLE rank_le row) = Sum.inl row := by
    apply (prefixEquiv rank_le).injective
    simp
  simp [rowPrefix, extendPrefixWithZeros, prefixWithZero, inverseEquation]

public theorem extendPrefixWithZeros_zeroTail {rank rows columns : Nat}
    (rank_le : rank ≤ rows) (basis : Matrix (Fin rank) (Fin columns) Int) :
    ∀ row : Fin rows, rank ≤ row.val → extendPrefixWithZeros rank_le basis row = 0 := by
  intro row afterRank
  apply funext
  intro column
  cases origin : (prefixEquiv rank_le).symm row with
  | inl prefixRow =>
      have rowEquation : prefixEquiv rank_le (Sum.inl prefixRow) = row := by
        simpa [origin] using (prefixEquiv rank_le).apply_symm_apply row
      have rowBefore : row.val < rank := by
        rw [← rowEquation]
        simp
      omega
  | inr tailRow =>
      simp [extendPrefixWithZeros, prefixWithZero, origin]

end NormalForms.Research.LLL.Internal.PrefixLift
