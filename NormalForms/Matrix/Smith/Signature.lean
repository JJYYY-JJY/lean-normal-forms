/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Matrix.Smith.Data
import all NormalForms.Matrix.Smith.Data

/-!
# Intrinsic Smith Signatures

A `SmithSignature` forgets the ordering and chosen associate representatives
of `SmithData`.  It retains dimensions, rank, and every nonzero invariant
factor as an associate class.  Unit factors are deliberately retained and the
zero tail is deliberately omitted.
-/

namespace NormalForms.Matrix.Smith

/--
The indexing-independent invariant carried by a Smith decomposition.

The multiset contains exactly `rank` nonzero factors, including units.
-/
public structure SmithSignature (R : Type u) [MonoidWithZero R] where
  rows : Nat
  cols : Nat
  rank : Nat
  factors : Multiset (Associates R)
  factor_card : factors.card = rank
  nonzero : ∀ factor ∈ factors, factor ≠ 0

@[ext] public theorem SmithSignature.ext {R : Type _} [MonoidWithZero R]
    {left right : SmithSignature R}
    (rows : left.rows = right.rows)
    (cols : left.cols = right.cols)
    (rank : left.rank = right.rank)
    (factors : left.factors = right.factors) :
    left = right := by
  cases left
  cases right
  cases rows
  cases cols
  cases rank
  cases factors
  rfl

namespace SmithSignature

/-- Rank of the right kernel, using the column convention. -/
@[expose] public def rightKernelRank {R : Type _} [MonoidWithZero R]
    (signature : SmithSignature R) : Nat :=
  signature.cols - signature.rank

/-- Rank of the left kernel. -/
@[expose] public def leftKernelRank {R : Type _} [MonoidWithZero R]
    (signature : SmithSignature R) : Nat :=
  signature.rows - signature.rank

/-- Rank of the free part of the cokernel. -/
@[expose] public def cokernelFreeRank {R : Type _} [MonoidWithZero R]
    (signature : SmithSignature R) : Nat :=
  signature.rows - signature.rank

@[simp] public theorem leftKernelRank_eq_cokernelFreeRank
    {R : Type _} [MonoidWithZero R] (signature : SmithSignature R) :
    signature.leftKernelRank = signature.cokernelFreeRank :=
  rfl

end SmithSignature

namespace SmithData

/-- The associate class of the `i`th nonzero diagonal entry. -/
@[expose] public def factorAt {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (data : SmithData m n R) (i : Fin data.rank) :
    Associates R :=
  Associates.mk (data.diagonal (Fin.castLE data.rank_le i))

/--
Forget ordering and representatives while retaining every nonzero factor,
including units.
-/
@[expose] public def signature {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (data : SmithData m n R) :
    SmithSignature R where
  rows := m
  cols := n
  rank := data.rank
  factors := Multiset.ofList (List.ofFn data.factorAt)
  factor_card := by
    simp
  nonzero := by
    intro factor hfactor
    rw [Multiset.mem_coe, List.mem_ofFn] at hfactor
    rcases hfactor with ⟨i, rfl⟩
    rw [factorAt, Associates.mk_ne_zero]
    exact data.nonzero_prefix (Fin.castLE data.rank_le i) i.2

@[simp] public theorem signature_rows {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (data : SmithData m n R) :
    data.signature.rows = m :=
  rfl

@[simp] public theorem signature_cols {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (data : SmithData m n R) :
    data.signature.cols = n :=
  rfl

@[simp] public theorem signature_rank {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (data : SmithData m n R) :
    data.signature.rank = data.rank :=
  rfl

@[simp] public theorem signature_factors {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (data : SmithData m n R) :
    data.signature.factors = Multiset.ofList (List.ofFn data.factorAt) :=
  rfl

end SmithData

/-- Intrinsic signature of a strong canonical `Fin` result. -/
@[expose] public noncomputable def SNFResultFin.smithSignature
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (result : SNFResultFin A) :
    SmithSignature R :=
  result.smithData.signature

/-- Intrinsic signature of a result over arbitrary finite index types. -/
@[expose] public noncomputable def SNFResult.smithSignature
    {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    SmithSignature R :=
  result.smithData.signature

@[simp] public theorem SNFResult.smithSignature_rows
    {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    result.smithSignature.rows = Fintype.card m :=
  rfl

@[simp] public theorem SNFResult.smithSignature_cols
    {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    result.smithSignature.cols = Fintype.card n :=
  rfl

@[simp] public theorem SNFResult.smithSignature_rank
    {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    result.smithSignature.rank = result.invariantFactors.length := by
  exact result.smithData_rank

/--
Changing row or column enumeration leaves dimensions, rank, and the associate
multiset unchanged.
-/
public theorem SNFResult.smithSignature_eq_of_indexing_change
    {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (source target : SNFResult A) :
    source.smithSignature = target.smithSignature :=
  congrArg SmithData.signature
    (source.smithData_eq_of_indexing_change target)

/--
Canonical Smith matrices related by invertible row and column transforms have
the same intrinsic signature.
-/
public theorem smithSignature_eq_of_two_sided_equiv
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A) (hB : IsSmithNormalFormFin B)
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {V : _root_.Matrix (Fin n) (Fin n) R}
    (hU : NormalForms.Matrix.Certificates.Unimodular U)
    (hV : NormalForms.Matrix.Certificates.Unimodular V)
    (equation : U * A * V = B) :
    (SmithData.ofSmithMatrix A hA).signature =
      (SmithData.ofSmithMatrix B hB).signature := by
  have hAB :
      A = B :=
    Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
      hA hB hU hV equation
  apply congrArg SmithData.signature
  apply SmithData.ext
  · change
      (smithInvariantFactorsFin A).length =
        (smithInvariantFactorsFin B).length
    rw [hAB]
  · funext i
    change smithDiagonalFin A i = smithDiagonalFin B i
    rw [hAB]

end NormalForms.Matrix.Smith
