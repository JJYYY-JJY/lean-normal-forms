/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Result
import all NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Euclidean.Int

/-!
# Executable row-rank data from Hermite shape

The rank is computed from the matrix itself.  Pivot columns are chosen only in
proofs, so the runtime decomposition does not eliminate data from `Prop`.
-/

namespace NormalForms.Research.LLL.Internal.RankDecomposition

open NormalForms.Matrix.Hermite
open NormalForms.Research.LLL

/-- Number of pivot rows in a recursive Hermite matrix. -/
private def hermiteRank : {m n : Nat} → Matrix (Fin m) (Fin n) Int → Nat
  | 0, _, _ => 0
  | _ + 1, 0, _ => 0
  | _ + 1, _ + 1, H =>
      if H 0 0 = 0 then hermiteRank (tailCols H)
      else Nat.succ (hermiteRank (lowerRight H))

@[simp] private theorem hermiteRank_zeroRows {n : Nat}
    (H : Matrix (Fin 0) (Fin n) Int) : hermiteRank H = 0 := by
  simp [hermiteRank]

@[simp] private theorem hermiteRank_zeroColumns {m : Nat}
    (H : Matrix (Fin m) (Fin 0) Int) : hermiteRank H = 0 := by
  cases m <;> rfl

private theorem hermiteRank_zeroColumn {m n : Nat}
    (H : Matrix (Fin (m + 1)) (Fin (n + 1)) Int) (zero : H 0 0 = 0) :
    hermiteRank H = hermiteRank (tailCols H) := by
  simp [hermiteRank, zero]

private theorem hermiteRank_pivot {m n : Nat}
    (H : Matrix (Fin (m + 1)) (Fin (n + 1)) Int) (nonzero : H 0 0 ≠ 0) :
    hermiteRank H = Nat.succ (hermiteRank (lowerRight H)) := by
  simp [hermiteRank, nonzero]

/-- Proof-only pivot profile whose rank agrees with the executable rank. -/
private structure HermiteRowProfile {m n : Nat}
    (H : Matrix (Fin m) (Fin n) Int) where
  rank : Nat
  rank_eq : rank = hermiteRank H
  rank_le_rows : rank ≤ m
  rank_le_columns : rank ≤ n
  pivots : Fin rank → Fin n
  pivots_strictMono : StrictMono pivots
  zero_tail : ∀ row : Fin m, rank ≤ row.val → ∀ column, H row column = 0
  pivot_positive : ∀ pivot : Fin rank,
    0 < H (Fin.castLE rank_le_rows pivot) (pivots pivot)
  prefix_zero : ∀ pivot : Fin rank, ∀ column,
    column < pivots pivot → H (Fin.castLE rank_le_rows pivot) column = 0
  below_zero : ∀ pivot : Fin rank, ∀ row,
    Fin.castLE rank_le_rows pivot < row → H row (pivots pivot) = 0

/-- Existence of a pivot profile is proved by the recursive Hermite witness. -/
private theorem existsProfileOfHermite {m n : Nat}
    {H : Matrix (Fin m) (Fin n) Int}
    (normal : IsHermiteNormalFormFin H) : Nonempty (HermiteRowProfile H) := by
  induction normal with
  | emptyRows A =>
      exact ⟨
        { rank := 0
          rank_eq := (hermiteRank_zeroRows A).symm
          rank_le_rows := by simp
          rank_le_columns := by simp
          pivots := fun pivot => Fin.elim0 pivot
          pivots_strictMono := fun pivot => Fin.elim0 pivot
          zero_tail := fun row => Fin.elim0 row
          pivot_positive := fun pivot => Fin.elim0 pivot
          prefix_zero := fun pivot => Fin.elim0 pivot
          below_zero := fun pivot => Fin.elim0 pivot }⟩
  | emptyCols A =>
      exact ⟨
        { rank := 0
          rank_eq := (hermiteRank_zeroColumns A).symm
          rank_le_rows := by simp
          rank_le_columns := by simp
          pivots := fun pivot => Fin.elim0 pivot
          pivots_strictMono := fun pivot => Fin.elim0 pivot
          zero_tail := by
            intro row _ column
            exact Fin.elim0 column
          pivot_positive := fun pivot => Fin.elim0 pivot
          prefix_zero := fun pivot => Fin.elim0 pivot
          below_zero := fun pivot => Fin.elim0 pivot }⟩
  | @zeroCol rows columns A firstZero tailNormal inductionHypothesis =>
      obtain ⟨tailProfile⟩ := inductionHypothesis
      have topZero : A 0 0 = 0 := firstZero 0
      have rankEq : hermiteRank A = hermiteRank (tailCols A) :=
        hermiteRank_zeroColumn A topZero
      exact ⟨
        { rank := tailProfile.rank
          rank_eq := tailProfile.rank_eq.trans rankEq.symm
          rank_le_rows := tailProfile.rank_le_rows
          rank_le_columns := tailProfile.rank_le_columns.trans (Nat.le_succ columns)
          pivots := fun pivot => (tailProfile.pivots pivot).succ
          pivots_strictMono := by
            intro left right before
            exact Fin.succ_lt_succ_iff.mpr <|
              tailProfile.pivots_strictMono before
          zero_tail := by
            intro row afterRank column
            cases column using Fin.cases with
            | zero => exact firstZero row
            | succ tailColumn =>
                exact tailProfile.zero_tail row afterRank tailColumn
          pivot_positive := by
            intro pivot
            simpa [tailCols] using tailProfile.pivot_positive pivot
          prefix_zero := by
            intro pivot column before
            cases column using Fin.cases with
            | zero => exact firstZero _
            | succ tailColumn =>
                have tailBefore :
                    tailColumn < tailProfile.pivots pivot := by
                  simpa using before
                simpa [tailCols] using
                  tailProfile.prefix_zero pivot tailColumn tailBefore
          below_zero := by
            intro pivot row below
            have tailBelow :
                Fin.castLE tailProfile.rank_le_rows pivot < row := by
              simpa using below
            simpa [tailCols] using
              tailProfile.below_zero pivot row tailBelow }⟩
  | @pivot rows columns A pivotNonzero pivotNormalized belowZero lowerNormal
      reduced inductionHypothesis =>
      obtain ⟨lowerProfile⟩ := inductionHypothesis
      have rankEq : hermiteRank A = Nat.succ (hermiteRank (lowerRight A)) :=
        hermiteRank_pivot A pivotNonzero
      have profileRankEq : Nat.succ lowerProfile.rank = hermiteRank A :=
        (congrArg Nat.succ lowerProfile.rank_eq).trans rankEq.symm
      have rankRows : Nat.succ lowerProfile.rank ≤ rows + 1 :=
        Nat.succ_le_succ lowerProfile.rank_le_rows
      have rankColumns : Nat.succ lowerProfile.rank ≤ columns + 1 :=
        Nat.succ_le_succ lowerProfile.rank_le_columns
      let pivots : Fin (Nat.succ lowerProfile.rank) → Fin (columns + 1) :=
        Fin.cases 0 (fun lower => (lowerProfile.pivots lower).succ)
      have topPositive : 0 < A 0 0 := by
        have nonnegative : 0 ≤ A 0 0 :=
          Int.nonneg_of_normalize_eq_self pivotNormalized.symm
        exact lt_of_le_of_ne nonnegative (Ne.symm pivotNonzero)
      exact ⟨
        { rank := Nat.succ lowerProfile.rank
          rank_eq := profileRankEq
          rank_le_rows := rankRows
          rank_le_columns := rankColumns
          pivots := pivots
          pivots_strictMono := by
            intro left right before
            cases left using Fin.cases with
            | zero =>
                cases right using Fin.cases with
                | zero => simp at before
                | succ right => simp [pivots]
            | succ left =>
                cases right using Fin.cases with
                | zero => simp at before
                | succ right =>
                    simp only [pivots, Fin.cases_succ]
                    exact Fin.succ_lt_succ_iff.mpr <|
                      lowerProfile.pivots_strictMono <|
                        Fin.succ_lt_succ_iff.mp before
          zero_tail := by
            intro row afterRank column
            cases row using Fin.cases with
            | zero =>
                simp at afterRank
            | succ lowerRow =>
                have lowerAfter : lowerProfile.rank ≤ lowerRow.val :=
                  Nat.succ_le_succ_iff.mp (by simpa using afterRank)
                cases column using Fin.cases with
                | zero => exact belowZero lowerRow
                | succ lowerColumn =>
                    exact lowerProfile.zero_tail lowerRow lowerAfter lowerColumn
          pivot_positive := by
            intro pivot
            cases pivot using Fin.cases with
            | zero =>
                simpa [pivots] using topPositive
            | succ lowerPivot =>
                simpa [pivots, lowerRight] using
                  lowerProfile.pivot_positive lowerPivot
          prefix_zero := by
            intro pivot column before
            cases pivot using Fin.cases with
            | zero =>
                simp [pivots] at before
            | succ lowerPivot =>
                cases column using Fin.cases with
                | zero =>
                    simpa using belowZero
                      (Fin.castLE lowerProfile.rank_le_rows lowerPivot)
                | succ lowerColumn =>
                    have lowerBefore : lowerColumn < lowerProfile.pivots lowerPivot := by
                      simpa [pivots] using before
                    simpa [pivots, lowerRight] using
                      lowerProfile.prefix_zero lowerPivot lowerColumn lowerBefore
          below_zero := by
            intro pivot row below
            cases pivot using Fin.cases with
            | zero =>
                cases row using Fin.cases with
                | zero => simp at below
                | succ lowerRow => exact belowZero lowerRow
            | succ lowerPivot =>
                cases row using Fin.cases with
                | zero => simp at below
                | succ lowerRow =>
                    have lowerBelow :
                        Fin.castLE lowerProfile.rank_le_rows lowerPivot < lowerRow := by
                      simpa using below
                    simpa [pivots, lowerRight] using
                      lowerProfile.below_zero lowerPivot lowerRow lowerBelow }⟩

/-- A proof-only chosen profile; its rank is proved equal to `hermiteRank`. -/
private noncomputable def profileOfHermite {m n : Nat}
    {H : Matrix (Fin m) (Fin n) Int} (normal : IsHermiteNormalFormFin H) :
    HermiteRowProfile H :=
  Classical.choice (existsProfileOfHermite normal)

private theorem foldlSumSquaresNonnegativeFrom {β : Type _}
    (values : List β) (term : β → Int) (accumulator : Int)
    (nonnegative : 0 ≤ accumulator) :
    0 ≤ values.foldl (fun total value => total + term value ^ 2) accumulator := by
  induction values generalizing accumulator with
  | nil => simpa using nonnegative
  | cons value values inductionHypothesis =>
      simp only [List.foldl_cons]
      have squareNonnegative : 0 ≤ term value ^ 2 := sq_nonneg _
      exact inductionHypothesis _ (Int.add_nonneg nonnegative squareNonnegative)

private theorem foldlSumSquaresPositiveFrom {β : Type _}
    (values : List β) (term : β → Int) (accumulator : Int)
    (positive : 0 < accumulator) :
    0 < values.foldl (fun total value => total + term value ^ 2) accumulator := by
  induction values generalizing accumulator with
  | nil => simpa using positive
  | cons value values inductionHypothesis =>
      simp only [List.foldl_cons]
      have squareNonnegative : 0 ≤ term value ^ 2 := sq_nonneg _
      exact inductionHypothesis _ (Int.add_pos_of_pos_of_nonneg positive squareNonnegative)

private theorem foldlSumSquaresPositiveOfMemberFrom {β : Type _}
    (values : List β) (term : β → Int) (accumulator : Int)
    (nonnegative : 0 ≤ accumulator) (target : β) (member : target ∈ values)
    (targetPositive : 0 < term target ^ 2) :
    0 < values.foldl (fun total value => total + term value ^ 2) accumulator := by
  induction values generalizing accumulator with
  | nil => cases member
  | cons value values inductionHypothesis =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with equal | member
      · subst value
        exact foldlSumSquaresPositiveFrom values term _
          (Int.add_pos_of_nonneg_of_pos nonnegative targetPositive)
      · have squareNonnegative : 0 ≤ term value ^ 2 := sq_nonneg _
        exact inductionHypothesis _ (Int.add_nonneg nonnegative squareNonnegative)
          member

private theorem gramMatrixTakeRows {rows columns : Nat}
    (basis : Hex.Matrix Int rows columns) (k : Nat) (k_le : k ≤ rows) :
    Hex.Matrix.gramMatrix (Hex.Matrix.takeRows basis k k_le) =
      Hex.Matrix.principalSubmatrix (Hex.Matrix.gramMatrix basis) k k_le := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro row row_lt
  apply Vector.ext
  intro column column_lt
  let rowPrefix : Fin k := ⟨row, row_lt⟩
  let columnPrefix : Fin k := ⟨column, column_lt⟩
  let rowFull : Fin rows := ⟨row, Nat.lt_of_lt_of_le row_lt k_le⟩
  let columnFull : Fin rows := ⟨column, Nat.lt_of_lt_of_le column_lt k_le⟩
  have rowEquation :
      Hex.Matrix.row (Hex.Matrix.takeRows basis k k_le) rowPrefix =
        Hex.Matrix.row basis rowFull := by
    apply Vector.ext
    intro entry entry_lt
    simp [Hex.Matrix.row, Hex.Matrix.takeRows, Hex.Matrix.ofFn, rowPrefix, rowFull]
  have columnEquation :
      Hex.Matrix.row (Hex.Matrix.takeRows basis k k_le) columnPrefix =
        Hex.Matrix.row basis columnFull := by
    apply Vector.ext
    intro entry entry_lt
    simp [Hex.Matrix.row, Hex.Matrix.takeRows, Hex.Matrix.ofFn, columnPrefix, columnFull]
  have dotEquation := congrArg₂ Vector.dotProduct rowEquation columnEquation
  simpa [Hex.Matrix.gramMatrix, Hex.Matrix.principalSubmatrix, Hex.Matrix.ofFn,
    rowPrefix, columnPrefix, rowFull, columnFull] using dotEquation

/-- Strict row pivots with positive diagonal entries certify dense independence. -/
private theorem independentOfPivotProfile {rows columns : Nat}
    (basis : Hex.Matrix Int rows columns) (pivots : Fin rows → Fin columns)
    (strict : StrictMono pivots)
    (below : ∀ row pivot : Fin rows, pivot < row → basis[row][pivots pivot] = 0)
    (positive : ∀ row : Fin rows, 0 < basis[row][pivots row]) :
    basis.independent := by
  apply Hex.GramSchmidt.Int.independent_of_det_positive basis
  intro k k_le _kPositive
  have gramPositive :
      0 < Hex.Matrix.det
        (Hex.Matrix.gramMatrix (Hex.Matrix.takeRows basis k k_le)) := by
    rw [Hex.Matrix.det_gramMatrix_eq_sum_minors_sq]
    let selected : Vector (Fin columns) k := Vector.ofFn fun index =>
      pivots (Hex.GramSchmidt.liftFinLE index k_le)
    have selectedMember : selected ∈ Hex.Matrix.selectedColumnTuples k columns := by
      rw [Hex.Matrix.mem_selectedColumnTuples_iff]
      intro left right before
      simpa [selected, Hex.GramSchmidt.liftFinLE] using
        strict (show Hex.GramSchmidt.liftFinLE left k_le <
          Hex.GramSchmidt.liftFinLE right k_le by
            simpa [Hex.GramSchmidt.liftFinLE] using before)
    let minor := Hex.Matrix.columnTupleMatrix
      (Hex.Matrix.takeRows basis k k_le)
      (Hex.Matrix.columnTupleVectorFn selected)
    have minorBelow : ∀ row column : Fin k, column.val < row.val →
        minor[row][column] = 0 := by
      intro row column before
      let fullRow := Hex.GramSchmidt.liftFinLE row k_le
      let fullColumn := Hex.GramSchmidt.liftFinLE column k_le
      have fullBefore : fullColumn < fullRow := by
        simpa [fullRow, fullColumn, Hex.GramSchmidt.liftFinLE] using before
      have zero := below fullRow fullColumn fullBefore
      simpa [minor, selected, Hex.Matrix.columnTupleMatrix,
        Hex.Matrix.columnTupleVectorFn, Hex.Matrix.takeRows, Hex.Matrix.ofFn,
        fullRow, fullColumn, Hex.GramSchmidt.liftFinLE] using zero
    have minorPositive : ∀ row : Fin k, 0 < minor[row][row] := by
      intro row
      let fullRow := Hex.GramSchmidt.liftFinLE row k_le
      have diagonal := positive fullRow
      simpa [minor, selected, Hex.Matrix.columnTupleMatrix,
        Hex.Matrix.columnTupleVectorFn, Hex.Matrix.takeRows, Hex.Matrix.ofFn,
        fullRow, Hex.GramSchmidt.liftFinLE] using diagonal
    have determinantPositive : 0 < Hex.Matrix.det minor :=
      Hex.Matrix.det_upperTriangular_pos_diag minor minorBelow minorPositive
    have squarePositive : 0 < Hex.Matrix.det minor ^ 2 := by
      nlinarith
    exact foldlSumSquaresPositiveOfMemberFrom
      (Hex.Matrix.selectedColumnTuples k columns)
      (fun columns => Hex.Matrix.det (Hex.Matrix.columnTupleMatrix
        (Hex.Matrix.takeRows basis k k_le)
        (Hex.Matrix.columnTupleVectorFn columns)))
      0 (by simp) selected selectedMember (by simpa [minor] using squarePositive)
  rwa [gramMatrixTakeRows basis k k_le] at gramPositive

/-- The nonzero Hermite prefix is independent in the executable dense model. -/
private theorem profilePrefixIndependent {m n : Nat}
    {H : Matrix (Fin m) (Fin n) Int} (profile : HermiteRowProfile H) :
    (toDense (rowPrefix profile.rank_le_rows H)).independent := by
  apply independentOfPivotProfile _ profile.pivots profile.pivots_strictMono
  · intro row pivot before
    have entryEquation :
        (toDense (rowPrefix profile.rank_le_rows H))[row][profile.pivots pivot] =
          H (Fin.castLE profile.rank_le_rows row) (profile.pivots pivot) := by
      calc
        _ = rowPrefix profile.rank_le_rows H row (profile.pivots pivot) := by
          simpa [toDense] using HexMatrixMathlib.matrixEquiv_symm_apply
            (rowPrefix profile.rank_le_rows H) row (profile.pivots pivot)
        _ = _ := rfl
    rw [entryEquation]
    exact profile.below_zero pivot (Fin.castLE profile.rank_le_rows row) <| by
      simpa using before
  · intro row
    have entryEquation :
        (toDense (rowPrefix profile.rank_le_rows H))[row][profile.pivots row] =
          H (Fin.castLE profile.rank_le_rows row) (profile.pivots row) := by
      calc
        _ = rowPrefix profile.rank_le_rows H row (profile.pivots row) := by
          simpa [toDense] using HexMatrixMathlib.matrixEquiv_symm_apply
            (rowPrefix profile.rank_le_rows H) row (profile.pivots row)
        _ = _ := rfl
    rw [entryEquation]
    exact profile.pivot_positive row

private theorem hermiteRankLeRows {m n : Nat}
    {H : Matrix (Fin m) (Fin n) Int} (normal : IsHermiteNormalFormFin H) :
    hermiteRank H ≤ m := by
  let profile := profileOfHermite normal
  rw [← profile.rank_eq]
  exact profile.rank_le_rows

private theorem hermitePrefixIndependent {m n : Nat}
    {H : Matrix (Fin m) (Fin n) Int} (normal : IsHermiteNormalFormFin H)
    (rank_le_rows : hermiteRank H ≤ m) :
    (toDense (rowPrefix rank_le_rows H)).independent := by
  let profile := profileOfHermite normal
  let castPivot : Fin (hermiteRank H) → Fin profile.rank :=
    fun pivot => Fin.cast profile.rank_eq.symm pivot
  let pivots : Fin (hermiteRank H) → Fin n :=
    fun pivot => profile.pivots (castPivot pivot)
  apply independentOfPivotProfile _ pivots
  · intro left right before
    exact profile.pivots_strictMono (by
      simpa [castPivot] using before)
  · intro row pivot before
    have rowEquation :
        Fin.castLE rank_le_rows row =
          Fin.castLE profile.rank_le_rows (castPivot row) := by
      ext
      rfl
    have entryEquation :
        (toDense (rowPrefix rank_le_rows H))[row][pivots pivot] =
          H (Fin.castLE rank_le_rows row) (pivots pivot) := by
      calc
        _ = rowPrefix rank_le_rows H row (pivots pivot) := by
          simpa [toDense] using HexMatrixMathlib.matrixEquiv_symm_apply
            (rowPrefix rank_le_rows H) row (pivots pivot)
        _ = _ := rfl
    rw [entryEquation, rowEquation]
    exact profile.below_zero (castPivot pivot)
      (Fin.castLE profile.rank_le_rows (castPivot row)) (by
        simpa [castPivot] using before)
  · intro row
    have rowEquation :
        Fin.castLE rank_le_rows row =
          Fin.castLE profile.rank_le_rows (castPivot row) := by
      ext
      rfl
    have entryEquation :
        (toDense (rowPrefix rank_le_rows H))[row][pivots row] =
          H (Fin.castLE rank_le_rows row) (pivots row) := by
      calc
        _ = rowPrefix rank_le_rows H row (pivots row) := by
          simpa [toDense] using HexMatrixMathlib.matrixEquiv_symm_apply
            (rowPrefix rank_le_rows H) row (pivots row)
        _ = _ := rfl
    rw [entryEquation, rowEquation]
    exact profile.pivot_positive (castPivot row)

private theorem hermiteZeroTail {m n : Nat}
    {H : Matrix (Fin m) (Fin n) Int} (normal : IsHermiteNormalFormFin H) :
    ∀ row : Fin m, hermiteRank H ≤ row.val → H row = 0 := by
  let profile := profileOfHermite normal
  intro row afterRank
  apply funext
  intro column
  exact profile.zero_tail row (by
    rw [profile.rank_eq]
    exact afterRank) column

/-- Internal executable seam between Hermite elimination and the total LLL wrapper. -/
public structure RowRankDecomposition {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) where
  rank : Nat
  rank_le_rows : rank ≤ m
  transform : Matrix (Fin m) (Fin m) Int
  transformCert : NormalForms.Matrix.Certificates.MatrixInverseCertificate transform
  echelon : Matrix (Fin m) (Fin n) Int
  equation : transform * basis = echelon
  prefixFullRank : FullRowRankWitness (rowPrefix rank_le_rows echelon)
  zeroTail : ∀ row : Fin m, rank ≤ row.val → echelon row = 0

/-- Compute an integer row-rank decomposition without leaking Hermite recursion. -/
public opaque rowRankDecomposition {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : RowRankDecomposition basis := by
  let hnf := hermiteNormalFormFin basis
  have rank_le_rows : hermiteRank hnf.H ≤ m :=
    hermiteRankLeRows hnf.isHermite
  exact
    { rank := hermiteRank hnf.H
      rank_le_rows := rank_le_rows
      transform := hnf.U
      transformCert := hnf.U_cert
      echelon := hnf.H
      equation := hnf.equation
      prefixFullRank := ⟨hermitePrefixIndependent hnf.isHermite rank_le_rows⟩
      zeroTail := hermiteZeroTail hnf.isHermite }

end NormalForms.Research.LLL.Internal.RankDecomposition
