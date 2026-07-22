/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.RankProfile
import all NormalForms.Research.ModularHNF.RankProfile
import all NormalForms.Matrix.Smith.Uniqueness
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Executable fraction-free rank-profile search

The runtime search enumerates only finite row/column selections.  Each
candidate derives its integer coefficients from a determinant and adjugate,
then checks the complete fraction-free profile contract.  Rational vector
spaces occur only in the erased completeness proof.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped BigOperators Matrix

theorem exists_rowMinor_of_cols_linearIndependent {m r : Nat}
    (M : _root_.Matrix (Fin m) (Fin r) Rat)
    (independent : LinearIndependent Rat M.col) :
    ∃ rows : Fin r ↪ Fin m, (M.submatrix rows id).det ≠ 0 := by
  have injective : Function.Injective M.mulVec :=
    _root_.Matrix.mulVec_injective_iff.mpr independent
  have kernel : LinearMap.ker M.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr injective
  obtain ⟨leftInverse, leftInverse_comp⟩ :=
    M.mulVecLin.exists_leftInverse_of_injective kernel
  let L : _root_.Matrix (Fin r) (Fin m) Rat :=
    LinearMap.toMatrix' leftInverse
  have leftMul : L * M = 1 := by
    calc
      L * M = LinearMap.toMatrix' leftInverse *
          LinearMap.toMatrix' (Matrix.toLin' M) := by
        rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix'
          (leftInverse.comp (Matrix.toLin' M)) := by
        rw [LinearMap.toMatrix'_comp]
      _ = LinearMap.toMatrix'
          (leftInverse.comp M.mulVecLin) := by
        rw [Matrix.toLin'_apply']
      _ = LinearMap.toMatrix' LinearMap.id := by rw [leftInverse_comp]
      _ = 1 := LinearMap.toMatrix'_id
  by_contra none
  push Not at none
  let identity : Fin r ↪ Fin r := Function.Embedding.refl _
  have determinantEq :=
    NormalForms.Matrix.Smith.Internal.det_submatrix_mul_sum_embeddings
      M.transpose L.transpose identity identity
  have productEq : M.transpose * L.transpose = (1 :
      _root_.Matrix (Fin r) (Fin r) Rat) := by
    rw [← _root_.Matrix.transpose_mul, leftMul]
    simp
  rw [productEq] at determinantEq
  have sumZero :
      (∑ rows : Fin r ↪ Fin m,
        (M.transpose.submatrix identity rows).det *
          ∏ i, L.transpose (rows i) (identity i)) = 0 := by
    apply Finset.sum_eq_zero
    intro rows _
    have transposeMinor :
        (M.transpose.submatrix identity rows).det =
          (M.submatrix rows id).det := by
      rw [← _root_.Matrix.det_transpose]
      congr 1
    rw [transposeMinor, none rows]
    simp
  rw [sumZero] at determinantEq
  simp [identity] at determinantEq

theorem exists_colEmbedding_linearIndependent_of_le_rank {m n k : Nat}
    (M : _root_.Matrix (Fin m) (Fin n) Rat) (rankAtLeast : k ≤ M.rank) :
    ∃ columns : Fin k ↪ Fin n,
      LinearIndependent Rat (fun i => M.col (columns i)) := by
  obtain ⟨basis, basisMem, _basisSpan, basisIndependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq Rat (Set.range M.col)
  have rankEq : Module.finrank Rat
      (Submodule.span Rat (Set.range M.col)) = M.rank := by
    rw [← _root_.Matrix.rank_eq_finrank_span_cols]
  have kLeFinrank : k ≤
      Module.finrank Rat (Submodule.span Rat (Set.range M.col)) := by
    rw [rankEq]
    exact rankAtLeast
  let injection : Fin k ↪
      Fin (Module.finrank Rat (Submodule.span Rat (Set.range M.col))) :=
    Fin.castLEEmb kLeFinrank
  choose source sourceEq using fun i => basisMem (injection i)
  have selectedIndependent :
      LinearIndependent Rat (fun i : Fin k => M.col (source i)) := by
    have restricted := basisIndependent.comp injection injection.injective
    have familyEq : basis ∘ injection =
        (fun i : Fin k => M.col (source i)) := by
      funext i
      exact (sourceEq i).symm
    rw [familyEq] at restricted
    exact restricted
  let columns : Fin k ↪ Fin n :=
    ⟨source, selectedIndependent.injective.of_comp⟩
  exact ⟨columns, by simpa [columns]⟩

theorem exists_nonsingular_minor_of_le_rank {m n k : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (rankAtLeast : k ≤ (A.map (Int.castRingHom Rat)).rank) :
    ∃ rows : Fin k ↪ Fin m, ∃ columns : Fin k ↪ Fin n,
      (A.submatrix rows columns).det ≠ 0 := by
  let M := A.map (Int.castRingHom Rat)
  obtain ⟨columns, independent⟩ :=
    exists_colEmbedding_linearIndependent_of_le_rank M rankAtLeast
  have selectedIndependent : LinearIndependent Rat
      (M.submatrix id columns).col := by
    change LinearIndependent Rat
      (fun i row => M row (columns i))
    change LinearIndependent Rat
      (fun i row => M row (columns i)) at independent
    exact independent
  obtain ⟨rows, minorNonzero⟩ :=
    exists_rowMinor_of_cols_linearIndependent
      (M.submatrix id columns) selectedIndependent
  refine ⟨rows, columns, ?_⟩
  intro integerZero
  apply minorNonzero
  have mappedZero := congrArg (Int.castRingHom Rat) integerZero
  have matrixEq :
      (M.submatrix id columns).submatrix rows id =
        (A.submatrix rows columns).map (Int.castRingHom Rat) := by
    ext i j
    rfl
  rw [matrixEq]
  change ((Int.castRingHom Rat).mapMatrix
    (A.submatrix rows columns)).det = 0
  rw [← (Int.castRingHom Rat).map_det]
  exact mappedZero

private structure OrderedSpanningFamily {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] {n : Nat}
    (v : Fin n → V) where
  rank : Nat
  columns : Fin rank ↪ Fin n
  columns_strictMono : StrictMono columns
  independent : LinearIndependent K (fun i => v (columns i))
  coefficients : Fin n → Fin rank → K
  combination : ∀ column,
    ∑ i, coefficients column i • v (columns i) = v column
  coefficients_zero_of_before : ∀ column i,
    column < columns i → coefficients column i = 0

private theorem exists_orderedSpanningFamily
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    ∀ {n : Nat} (v : Fin n → V),
      Nonempty (OrderedSpanningFamily (K := K) v) := by
  classical
  intro n
  induction n with
  | zero =>
      intro v
      exact ⟨
        { rank := 0
          columns := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
          columns_strictMono := fun i => Fin.elim0 i
          independent := linearIndependent_empty_type
          coefficients := Fin.elim0
          combination := fun column => Fin.elim0 column
          coefficients_zero_of_before := fun column => Fin.elim0 column }⟩
  | succ n ih =>
      intro v
      let initial : Fin n → V := fun column => v column.castSucc
      obtain ⟨old⟩ := ih initial
      by_cases lastMem : v (Fin.last n) ∈
          Submodule.span K (Set.range fun i => initial (old.columns i))
      · obtain ⟨lastCoefficients, lastCombination⟩ :=
          (Submodule.mem_span_range_iff_exists_fun K).mp lastMem
        let columns : Fin old.rank ↪ Fin (n + 1) :=
          { toFun := fun i => (old.columns i).castSucc
            inj' := fun _ _ equal => old.columns.injective (Fin.castSucc_inj.mp equal) }
        let coefficients : Fin (n + 1) → Fin old.rank → K :=
          Fin.lastCases lastCoefficients old.coefficients
        exact ⟨
          { rank := old.rank
            columns := columns
            columns_strictMono := by
              intro i j before
              change (old.columns i).val < (old.columns j).val
              exact old.columns_strictMono before
            independent := by
              simpa [columns, initial] using old.independent
            coefficients := coefficients
            combination := by
              intro column
              cases column using Fin.lastCases with
              | last =>
                  simpa [coefficients, columns, initial] using lastCombination
              | cast column =>
                  simpa [coefficients, columns, initial] using
                    old.combination column
            coefficients_zero_of_before := by
              intro column i before
              cases column using Fin.lastCases with
              | last =>
                  have bound := (old.columns i).isLt
                  change n < (old.columns i).val at before
                  omega
              | cast column =>
                  have oldBefore : column < old.columns i := by
                    exact before
                  simpa [coefficients] using
                    old.coefficients_zero_of_before column i oldBefore } ⟩
      · let columnsFun : Fin (old.rank + 1) → Fin (n + 1) :=
          Fin.snoc (fun i => (old.columns i).castSucc) (Fin.last n)
        have columnsStrict : StrictMono columnsFun := by
          intro i j before
          cases j using Fin.lastCases with
          | last =>
              cases i using Fin.lastCases with
              | last => simp at before
              | cast i =>
                  simp [columnsFun]
          | cast j =>
              cases i using Fin.lastCases with
              | last =>
                  have bound := j.isLt
                  change old.rank < j.val at before
                  omega
              | cast i =>
                  simpa [columnsFun] using
                    old.columns_strictMono before
        let columns : Fin (old.rank + 1) ↪ Fin (n + 1) :=
          ⟨columnsFun, columnsStrict.injective⟩
        let coefficients : Fin (n + 1) → Fin (old.rank + 1) → K :=
          Fin.lastCases
            (Fin.snoc (fun _ => 0) 1)
            (fun column => Fin.snoc (old.coefficients column) 0)
        exact ⟨
          { rank := old.rank + 1
            columns := columns
            columns_strictMono := columnsStrict
            independent := by
              have appended := old.independent.finSnoc lastMem
              have familyEq : (fun i => v (columns i)) =
                  Fin.snoc (fun i => initial (old.columns i))
                    (v (Fin.last n)) := by
                funext i
                cases i using Fin.lastCases <;>
                  simp [columns, columnsFun, initial]
              rw [familyEq]
              exact appended
            coefficients := coefficients
            combination := by
              intro column
              cases column using Fin.lastCases with
              | last =>
                  rw [Fin.sum_univ_castSucc]
                  simp [coefficients, columns, columnsFun]
              | cast column =>
                  rw [Fin.sum_univ_castSucc]
                  simpa [coefficients, columns, columnsFun, initial] using
                    old.combination column
            coefficients_zero_of_before := by
              intro column i before
              cases column using Fin.lastCases with
              | last =>
                  have bound := (columns i).isLt
                  change n < (columns i).val at before
                  omega
              | cast column =>
                  cases i using Fin.lastCases with
                  | last =>
                      simp [coefficients]
                  | cast i =>
                      have oldBefore : column < old.columns i := by
                        simpa [columns, columnsFun] using before
                      simpa [coefficients] using
                        old.coefficients_zero_of_before column i oldBefore } ⟩

/-- Integer Cramer numerators for one row/column selection. -/
@[expose] def adjugateCoefficients {m n r : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (rows : Fin r → Fin m) (columns : Fin r → Fin n) :
    Fin n → Fin r → Int :=
  fun column i => ∑ j,
    (A.submatrix rows columns).adjugate i j * A (rows j) column

/-- Finite data searched before the fraction-free equations are checked. -/
structure RankProfileSelection (m n : Nat) where
  rank : Fin (min m n + 1)
  pivotColumns : Fin rank → Fin n
  pivotRows : Fin rank → Fin m
deriving DecidableEq

@[expose] def RankProfileSelection.minor {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (selection : RankProfileSelection m n) :
    _root_.Matrix (Fin selection.rank) (Fin selection.rank) Int :=
  A.submatrix selection.pivotRows selection.pivotColumns

@[expose] def RankProfileSelection.coefficients {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (selection : RankProfileSelection m n) :
    Fin n → Fin selection.rank → Int :=
  adjugateCoefficients A selection.pivotRows selection.pivotColumns

/-- The complete, decidable, fraction-free contract for a selection. -/
@[expose] def RankProfileSelection.IsValid {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (selection : RankProfileSelection m n) : Prop :=
  StrictMono selection.pivotColumns ∧
    Function.Injective selection.pivotRows ∧
    (selection.minor A).det ≠ 0 ∧
    (∀ row column,
      (selection.minor A).det * A row column =
        ∑ i, selection.coefficients A column i *
          A row (selection.pivotColumns i)) ∧
    ∀ column i, column < selection.pivotColumns i →
      selection.coefficients A column i = 0

instance {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (selection : RankProfileSelection m n) :
    Decidable (selection.IsValid A) := by
  unfold RankProfileSelection.IsValid
  infer_instance

/-- Promote a checked finite selection to the strong profile interface. -/
def RankProfileSelection.toProfile {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (selection : RankProfileSelection m n)
    (valid : selection.IsValid A) : FractionFreeRankProfile A :=
  let columns : Fin selection.rank ↪ Fin n :=
    ⟨selection.pivotColumns, valid.1.injective⟩
  let rows : Fin selection.rank ↪ Fin m :=
    ⟨selection.pivotRows, valid.2.1⟩
  { rank := selection.rank
    rank_le_rows := by
      have bound := selection.rank.isLt
      omega
    rank_le_columns := by
      have bound := selection.rank.isLt
      omega
    pivotColumns := columns
    pivotColumns_strictMono := valid.1
    pivotRows := rows
    minor_ne_zero := valid.2.2.1
    coefficients := selection.coefficients A
    column_identity := valid.2.2.2.1
    coefficients_zero_of_before := valid.2.2.2.2 }

/-- The finite integer search space contains a valid selection for every matrix. -/
theorem exists_validRankProfileSelection {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    ∃ selection : RankProfileSelection m n, selection.IsValid A := by
  classical
  let M := A.map (Int.castRingHom Rat)
  obtain ⟨basis⟩ := exists_orderedSpanningFamily (K := Rat) M.col
  have rankLeRows : basis.rank ≤ m := by
    have bound := basis.independent.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using bound
  have rankLeColumns : basis.rank ≤ n := by
    simpa using Fintype.card_le_of_injective basis.columns
      basis.columns.injective
  let selected : _root_.Matrix (Fin m) (Fin basis.rank) Rat :=
    M.submatrix id basis.columns
  have selectedIndependent : LinearIndependent Rat selected.col := by
    change LinearIndependent Rat
      (fun i row => M row (basis.columns i))
    have independent := basis.independent
    change LinearIndependent Rat
      (fun i row => M row (basis.columns i)) at independent
    exact independent
  obtain ⟨rows, minorRatNonzero⟩ :=
    exists_rowMinor_of_cols_linearIndependent selected selectedIndependent
  let B := A.submatrix rows basis.columns
  have minorNonzero : B.det ≠ 0 := by
    intro integerZero
    apply minorRatNonzero
    have matrixEq : selected.submatrix rows id =
        B.map (Int.castRingHom Rat) := by
      ext i j
      rfl
    rw [matrixEq]
    change ((Int.castRingHom Rat).mapMatrix B).det = 0
    rw [← (Int.castRingHom Rat).map_det, integerZero]
    simp
  let coefficients :=
    adjugateCoefficients A rows basis.columns
  have coefficientCast : ∀ column i,
      (coefficients column i : Rat) =
        (B.det : Rat) * basis.coefficients column i := by
    intro column i
    let BRat := B.map (Int.castRingHom Rat)
    let selectedEntries : Fin basis.rank → Rat :=
      fun j => M (rows j) column
    let rationalCoefficients := basis.coefficients column
    have selectedEquation :
        BRat.mulVec rationalCoefficients = selectedEntries := by
      funext j
      have entry := congrFun (basis.combination column) (rows j)
      simpa [BRat, B, M, selectedEntries, rationalCoefficients,
        _root_.Matrix.mulVec, dotProduct, mul_comm] using entry
    have adjugateMap : BRat.adjugate =
        B.adjugate.map (Int.castRingHom Rat) := by
      exact ((Int.castRingHom Rat).map_adjugate B).symm
    calc
      (coefficients column i : Rat) =
          (BRat.adjugate.mulVec selectedEntries) i := by
        rw [adjugateMap]
        simp [coefficients, adjugateCoefficients, B,
          selectedEntries, M, _root_.Matrix.mulVec, dotProduct]
      _ = (BRat.adjugate.mulVec
          (BRat.mulVec rationalCoefficients)) i := by
        rw [selectedEquation]
      _ = ((BRat.adjugate * BRat).mulVec rationalCoefficients) i := by
        rw [_root_.Matrix.mulVec_mulVec]
      _ = ((BRat.det • (1 : _root_.Matrix (Fin basis.rank)
          (Fin basis.rank) Rat)).mulVec rationalCoefficients) i := by
        rw [_root_.Matrix.adjugate_mul]
      _ = (B.det : Rat) * basis.coefficients column i := by
        rw [_root_.Matrix.smul_mulVec, _root_.Matrix.one_mulVec]
        change BRat.det * rationalCoefficients i =
          (B.det : Rat) * basis.coefficients column i
        have determinantMap := (Int.castRingHom Rat).map_det B
        change (B.det : Rat) = BRat.det at determinantMap
        rw [← determinantMap]
  let selection : RankProfileSelection m n :=
    { rank := ⟨basis.rank, by omega⟩
      pivotColumns := basis.columns
      pivotRows := rows }
  refine ⟨selection, ?_⟩
  refine ⟨basis.columns_strictMono, rows.injective, ?_, ?_, ?_⟩
  · simpa [selection, RankProfileSelection.minor, B] using minorNonzero
  · intro row column
    change B.det * A row column =
      ∑ i, coefficients column i * A row (basis.columns i)
    apply Int.cast_injective (α := Rat)
    simp only [Int.cast_mul, Int.cast_sum]
    change (B.det : Rat) * (A row column : Rat) =
      ∑ i, (coefficients column i : Rat) *
        (A row (basis.columns i) : Rat)
    simp_rw [coefficientCast column]
    have entry : M row column =
        ∑ i, basis.coefficients column i *
          M row (basis.columns i) := by
      simpa [M, _root_.Matrix.col, smul_eq_mul] using
        (congrFun (basis.combination column) row).symm
    calc
      (B.det : Rat) * (A row column : Rat) =
          (B.det : Rat) * M row column := by rfl
      _ = (B.det : Rat) *
          ∑ i, basis.coefficients column i *
            M row (basis.columns i) := by rw [entry]
      _ = ∑ i, ((B.det : Rat) * basis.coefficients column i) *
            (A row (basis.columns i) : Rat) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [M]
        ring
  · intro column i before
    change coefficients column i = 0
    apply Int.cast_injective (α := Rat)
    rw [coefficientCast,
      basis.coefficients_zero_of_before column i before]
    simp

def allFinFunctions :
    (k n : Nat) → List (Fin k → Fin n)
  | 0, _ => [Fin.elim0]
  | k + 1, n =>
      (List.ofFn (fun i : Fin n => i)).flatMap fun head =>
        (allFinFunctions k n).map fun tail => Fin.cons head tail

private theorem mem_allFinFunctions {k n : Nat}
    (f : Fin k → Fin n) : f ∈ allFinFunctions k n := by
  induction k with
  | zero =>
      simp only [allFinFunctions, List.mem_singleton]
      funext i
      exact Fin.elim0 i
  | succ k ih =>
      rw [allFinFunctions, List.mem_flatMap]
      refine ⟨f 0, List.mem_ofFn.mpr ⟨f 0, rfl⟩, ?_⟩
      rw [List.mem_map]
      exact ⟨Fin.tail f, ih (Fin.tail f), Fin.cons_self_tail f⟩

def rankProfileCandidates (m n : Nat) :
    List (RankProfileSelection m n) :=
  (List.ofFn (fun rank : Fin (min m n + 1) => rank)).flatMap
    fun (rank : Fin (min m n + 1)) =>
    (allFinFunctions rank.val n).flatMap fun columns =>
      (allFinFunctions rank.val m).map fun rows =>
        { rank := rank
          pivotColumns := columns
          pivotRows := rows }

private theorem mem_rankProfileCandidates {m n : Nat}
    (selection : RankProfileSelection m n) :
    selection ∈ rankProfileCandidates m n := by
  rw [rankProfileCandidates, List.mem_flatMap]
  refine ⟨selection.rank, List.mem_ofFn.mpr ⟨selection.rank, rfl⟩, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨selection.pivotColumns,
    mem_allFinFunctions selection.pivotColumns, ?_⟩
  rw [List.mem_map]
  refine ⟨selection.pivotRows,
    mem_allFinFunctions selection.pivotRows, ?_⟩
  cases selection
  rfl

/-- Exhaustive deterministic search over finite row and column selections. -/
@[expose] def searchRankProfile? {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    Option (RankProfileSelection m n) :=
  (rankProfileCandidates m n).find?
    (fun selection => decide (selection.IsValid A))

theorem searchRankProfile_isSome {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (searchRankProfile? A).isSome = true := by
  rw [searchRankProfile?, List.find?_isSome]
  obtain ⟨selection, valid⟩ := exists_validRankProfileSelection A
  refine ⟨selection, ?_, decide_eq_true valid⟩
  exact mem_rankProfileCandidates selection

/-- The selection returned by the exhaustive search satisfies its checked contract. -/
theorem searchRankProfile_valid {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    ((searchRankProfile? A).get (searchRankProfile_isSome A)).IsValid A := by
  let found := (searchRankProfile? A).get (searchRankProfile_isSome A)
  have foundEq : searchRankProfile? A = some found :=
    (Option.some_get (searchRankProfile_isSome A)).symm
  have checked : decide (found.IsValid A) = true := by
    exact List.find?_some (p := fun
        (selection : RankProfileSelection m n) =>
      decide (selection.IsValid A))
      (by simpa [searchRankProfile?] using foundEq)
  exact of_decide_eq_true checked

/-- A total executable fraction-free rank profile. -/
@[expose] def fractionFreeRankProfile {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    FractionFreeRankProfile A :=
  let found := (searchRankProfile? A).get (searchRankProfile_isSome A)
  found.toProfile (searchRankProfile_valid A)

/-- General rectangular and rank-deficient modular HNF. -/
@[expose] def integerHermiteNormalFormModular {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    NormalForms.Matrix.Hermite.HNFResultFin A :=
  integerHermiteNormalFormModularWithProfile A
    (fractionFreeRankProfile A)

theorem integerHermiteNormalFormModular_eq_reference {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (integerHermiteNormalFormModular A).H =
      (NormalForms.Matrix.Hermite.hermiteNormalFormFin A).H :=
  integerHermiteNormalFormModularWithProfile_eq_reference A
    (fractionFreeRankProfile A)

end NormalForms.Research.ModularHNF
