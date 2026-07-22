/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Reference
import all NormalForms.Research.ModularHNF.Coordinate
import all NormalForms.Research.ModularHNF.Determinant

/-!
# Semantic correctness of the determinant-modulus kernel

The live augmented row lattice is compared with the certified canonical HNF.
At every column, coordinate divisibility identifies the computed gcd with the
reference pivot.  The suffix determinant recurrence then validates the next
implicit modular basis.  Iteration proves that the raw modular candidate is
exactly the canonical HNF, without treating the core algorithm as a fallback.
-/

namespace NormalForms.Research.ModularHNF

open scoped BigOperators Matrix
open NormalForms
open NormalForms.Matrix.Hermite

theorem processedShape_of_columns_eq {m n k : Nat}
    {columns_le_rows : n ≤ m}
    {A B : _root_.Matrix (Fin m) (Fin n) Int}
    (shape : ProcessedHermiteShape columns_le_rows A k)
    (columnEq : ∀ row column, column.val < k → B row column = A row column) :
    ProcessedHermiteShape columns_le_rows B k := by
  intro column before
  exact ColumnHermiteShape.of_column_eq (shape column before)
    (fun row => columnEq row column before)

theorem prefixRowsZero_of_fullShape {m n k : Nat}
    {columns_le_rows : n ≤ m}
    {H : _root_.Matrix (Fin m) (Fin n) Int}
    (shape : ProcessedHermiteShape columns_le_rows H n) : PrefixRowsZero H k := by
  intro row rowAfter column before
  have columnShape := shape column column.isLt
  apply columnShape.below_zero row
  change column.val < row.val
  omega

theorem stage_reference_pivot {m n : Nat}
    (columns_le_rows : n ≤ m)
    (state : RawModularRun m n) (column : Fin n)
    (prefixZero : PrefixRowsZero state.candidate column.val)
    (processedShape :
      ProcessedHermiteShape columns_le_rows state.candidate column.val)
    (modulusPositive : 0 < state.finalModulus)
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (referenceShape :
      ProcessedHermiteShape columns_le_rows H n)
    (latticeEq :
      augmentedRowSpan state.candidate state.finalModulus column.val =
        rowSpan H) :
    let pivot : Fin m := Fin.castLE columns_le_rows column
    let modulus := state.finalModulus
    let prepared :=
      if state.candidate pivot column = 0 then
        Internal.setEntry state.candidate pivot column modulus
      else
        state.candidate
    let below := Internal.reduceBelow pivot column modulus
      (List.finRange m) prepared
    let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
    gcdData.gcd = H pivot column := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      Internal.setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := Internal.reduceBelow pivot column modulus
    (List.finRange m) prepared
  let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
  let scaled := Internal.scalePivotSuffix below.1 pivot column
    gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      Internal.setEntry scaled pivot column modulus
    else
      scaled
  have columnBeforeEnd : column.val < n := column.isLt
  have pivotValue : pivot.val = column.val := by simp [pivot]
  have preparedPrefix : PrefixRowsZero prepared column.val := by
    by_cases pivotZero : state.candidate pivot column = 0
    · rw [show prepared = Internal.setEntry state.candidate pivot column modulus by
        simp [prepared, pivotZero]]
      exact Internal.setEntry_prefixRowsZero state.candidate pivot column modulus
        prefixZero
    · rw [show prepared = state.candidate by simp [prepared, pivotZero]]
      exact prefixZero
  have belowPrefix : PrefixRowsZero below.1 column.val :=
    Internal.reduceBelow_prefixRowsZero pivot column modulus
      (List.finRange m) prepared preparedPrefix
  have belowZero : ∀ row, pivot < row → below.1 row column = 0 :=
    Internal.reduceBelow_finRange_column_zero pivot column modulus
      (by simpa [modulus] using modulusPositive) prepared
  have belowColumns : ∀ row currentColumn,
      currentColumn.val < column.val →
      below.1 row currentColumn = state.candidate row currentColumn := by
    intro row currentColumn before
    have currentBefore : currentColumn < column := before
    have preparedEq : prepared row currentColumn =
        state.candidate row currentColumn := by
      by_cases pivotZero : state.candidate pivot column = 0
      · rw [show prepared = Internal.setEntry state.candidate pivot column modulus by
          simp [prepared, pivotZero]]
        by_cases rowEq : row = pivot
        · subst row
          exact Internal.setEntry_apply_of_column_ne state.candidate pivot
            column currentColumn modulus currentBefore.ne
        · exact Internal.setEntry_apply_of_row_ne state.candidate pivot row
            column currentColumn modulus rowEq
      · rw [show prepared = state.candidate by simp [prepared, pivotZero]]
    calc
      below.1 row currentColumn = prepared row currentColumn :=
        Internal.reduceBelow_apply_before pivot row column currentColumn
          modulus currentBefore (List.finRange m) prepared
      _ = state.candidate row currentColumn := preparedEq
  have belowShape : ProcessedHermiteShape columns_le_rows
      below.1 column.val :=
    processedShape_of_columns_eq processedShape belowColumns
  have beforeSpan : augmentedRowSpan below.1 modulus column.val =
      rowSpan H := by
    calc
      augmentedRowSpan below.1 modulus column.val =
          augmentedRowSpan state.candidate modulus column.val := by
        simpa [pivot, modulus, prepared, below] using
          (Internal.stage_beforeScale_augmentedRowSpan columns_le_rows state
            column prefixZero)
      _ = rowSpan H := by simpa [modulus] using latticeEq
  have gcdDvdReference : gcdData.gcd ∣ H pivot column := by
    apply coordinate_dvd_of_mem_augmented columns_le_rows below.1
      columnBeforeEnd belowShape pivot column pivotValue rfl belowZero
      modulus gcdData.gcd
    · simpa [gcdData] using
        (ComputableEuclideanOps.xgcd_gcd_dvd_left
          (below.1 pivot column) modulus)
    · simpa [gcdData] using
        (ComputableEuclideanOps.xgcd_gcd_dvd_right
          (below.1 pivot column) modulus)
    · rw [beforeSpan]
      exact row_mem_rowSpan H pivot
    · intro currentColumn before
      have currentShape := referenceShape currentColumn currentColumn.isLt
      have currentPivotBefore :
          Fin.castLE columns_le_rows currentColumn < pivot := by
        change currentColumn.val < column.val
        exact before
      exact currentShape.below_zero pivot currentPivotBefore
  have restoredPrefix : PrefixRowsZero restored column.val := by
    simpa [gcdData, scaled, restored] using
      (Internal.scaleAndRestore_prefixRowsZero below.1 pivot column modulus
        belowPrefix)
  have restoredPivot : restored pivot column = gcdData.gcd := by
    simpa [gcdData, scaled, restored] using
      (Internal.scaleAndRestore_pivot_column below.1 pivot column modulus
        (by simpa [modulus] using modulusPositive))
  have restoredRowMem : restored.row pivot ∈ rowSpan H := by
    rw [← beforeSpan]
    exact Internal.scaleAndRestore_rowSpan_le_augmented below.1 pivot column
      modulus (fun currentColumn before =>
        belowPrefix pivot (by omega) currentColumn before)
      (row_mem_rowSpan restored pivot)
  have referenceDvdGcd : H pivot column ∣ gcdData.gcd := by
    rw [← restoredPivot]
    apply coordinate_dvd_of_mem_augmented columns_le_rows H
      columnBeforeEnd
      (fun currentColumn before => referenceShape currentColumn
        (lt_trans before columnBeforeEnd))
      pivot column pivotValue rfl
      (referenceShape column column.isLt).below_zero
      0 (H pivot column)
    · exact dvd_refl _
    · exact dvd_zero _
    · exact Submodule.mem_sup_left restoredRowMem
    · intro currentColumn before
      exact restoredPrefix pivot (by omega) currentColumn before
  exact dvd_antisymm_of_normalize_eq
    (ComputableEuclideanOps.xgcd_gcd_normalized
      (below.1 pivot column) modulus).symm
    (referenceShape column column.isLt).pivot_normalized.symm
    gcdDvdReference referenceDvdGcd

theorem stage_referenceInvariant {m n : Nat}
    (columns_le_rows : n ≤ m)
    (state : RawModularRun m n) (column : Fin n)
    (prefixZero : PrefixRowsZero state.candidate column.val)
    (processedShape :
      ProcessedHermiteShape columns_le_rows state.candidate column.val)
    (modulusPositive : 0 < state.finalModulus)
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (referenceShape :
      ProcessedHermiteShape columns_le_rows H n)
    (latticeEq :
      augmentedRowSpan state.candidate state.finalModulus column.val =
        rowSpan H)
    (detDivides :
      (suffixSquare H columns_le_rows column.val).det ∣
        state.finalModulus) :
    augmentedRowSpan
        (Internal.stage columns_le_rows state column).candidate
        (Internal.stage columns_le_rows state column).finalModulus
        (column.val + 1) = rowSpan H ∧
      (suffixSquare H columns_le_rows (column.val + 1)).det ∣
        (Internal.stage columns_le_rows state column).finalModulus := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      Internal.setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := Internal.reduceBelow pivot column modulus
    (List.finRange m) prepared
  let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
  have gcdEq : gcdData.gcd = H pivot column := by
    simpa [pivot, modulus, prepared, below, gcdData] using
      (stage_reference_pivot columns_le_rows state column prefixZero
        processedShape modulusPositive H referenceShape latticeEq)
  have determinantStep :
      (suffixSquare H columns_le_rows column.val).det =
        H pivot column *
          (suffixSquare H columns_le_rows (column.val + 1)).det := by
    simpa [pivot] using
      (suffixSquare_det_step H columns_le_rows referenceShape column.isLt)
  have referencePivotNonzero : H pivot column ≠ 0 := by
    simpa [pivot] using
      ne_of_gt (referenceShape column column.isLt).pivot_positive
  have nextDivides :
      (suffixSquare H columns_le_rows (column.val + 1)).det ∣
        modulus / gcdData.gcd := by
    rcases detDivides with ⟨coefficient, modulusEq⟩
    have modulusEq' :
        modulus = (suffixSquare H columns_le_rows column.val).det *
          coefficient := by
      simpa [modulus] using modulusEq
    refine ⟨coefficient, ?_⟩
    rw [gcdEq, modulusEq', determinantStep, mul_assoc]
    exact (Int.mul_ediv_cancel_left _ referencePivotNonzero)
  have referencePrefix : PrefixRowsZero H (column.val + 1) :=
    prefixRowsZero_of_fullShape referenceShape
  have nextSuffixReference :
      suffixModule (modulus / gcdData.gcd) (column.val + 1) ≤ rowSpan H := by
    rw [suffixModule, Submodule.span_le]
    rintro _ ⟨currentColumn, rfl⟩
    rcases nextDivides with ⟨coefficient, quotientEq⟩
    have determinantMem := suffixDet_smul_single_mem_rowSpan H
      columns_le_rows (column.val + 1) referencePrefix currentColumn
    rw [quotientEq]
    simpa [mul_smul, mul_comm] using
      Submodule.smul_mem (rowSpan H) coefficient determinantMem
  have nextSuffix :
      suffixModule (modulus / gcdData.gcd) (column.val + 1) ≤
        augmentedRowSpan state.candidate modulus column.val := by
    rw [latticeEq]
    exact nextSuffixReference
  have stageLattice := Internal.stage_augmentedRowSpan_eq_next
    columns_le_rows state column modulusPositive prefixZero
  constructor
  · exact (stageLattice (by
        simpa [pivot, modulus, prepared, below, gcdData] using nextSuffix)).trans
      latticeEq
  · simpa [Internal.stage, pivot, modulus, prepared, below, gcdData] using
      nextDivides

public theorem fullColumnShape_unique_of_rowSpan_eq {m n : Nat}
    (columns_le_rows : n ≤ m)
    (A H : _root_.Matrix (Fin m) (Fin n) Int)
    (shapeA : ProcessedHermiteShape columns_le_rows A n)
    (shapeH : ProcessedHermiteShape columns_le_rows H n)
    (spanEq : rowSpan A = rowSpan H) : A = H := by
  have columnEq : ∀ k, ∀ beforeEnd : k < n, ∀ row : Fin m,
      A row ⟨k, beforeEnd⟩ = H row ⟨k, beforeEnd⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro beforeEnd row
        let column : Fin n := ⟨k, beforeEnd⟩
        let pivot : Fin m := Fin.castLE columns_le_rows column
        have pivotValue : pivot.val = column.val := by simp [pivot]
        have shapeAColumn := shapeA column column.isLt
        have shapeHColumn := shapeH column column.isLt
        have aDvdH : A pivot column ∣ H pivot column := by
          apply coordinate_dvd_of_mem_augmented columns_le_rows A
            beforeEnd
            (fun currentColumn before => shapeA currentColumn
              (lt_trans before beforeEnd))
            pivot column pivotValue rfl shapeAColumn.below_zero
            0 (A pivot column)
          · exact dvd_refl _
          · exact dvd_zero _
          · apply Submodule.mem_sup_left
            rw [spanEq]
            exact row_mem_rowSpan H pivot
          · intro currentColumn before
            have currentShape := shapeH currentColumn currentColumn.isLt
            apply currentShape.below_zero pivot
            change currentColumn.val < pivot.val
            simpa [pivot, column] using before
        have hDvdA : H pivot column ∣ A pivot column := by
          apply coordinate_dvd_of_mem_augmented columns_le_rows H
            beforeEnd
            (fun currentColumn before => shapeH currentColumn
              (lt_trans before beforeEnd))
            pivot column pivotValue rfl shapeHColumn.below_zero
            0 (H pivot column)
          · exact dvd_refl _
          · exact dvd_zero _
          · apply Submodule.mem_sup_left
            rw [← spanEq]
            exact row_mem_rowSpan A pivot
          · intro currentColumn before
            have currentShape := shapeA currentColumn currentColumn.isLt
            apply currentShape.below_zero pivot
            change currentColumn.val < pivot.val
            simpa [pivot, column] using before
        have pivotEq : A pivot column = H pivot column :=
          dvd_antisymm_of_normalize_eq
            shapeAColumn.pivot_normalized.symm
            shapeHColumn.pivot_normalized.symm aDvdH hDvdA
        by_cases rowBefore : row < pivot
        · have differenceMem : A.row row - H.row row ∈ rowSpan A := by
            apply Submodule.sub_mem
            · exact row_mem_rowSpan A row
            · rw [spanEq]
              exact row_mem_rowSpan H row
          have differenceDvd : A pivot column ∣
              (A.row row - H.row row) column := by
            apply coordinate_dvd_of_mem_augmented columns_le_rows A
              beforeEnd
              (fun currentColumn before => shapeA currentColumn
                (lt_trans before beforeEnd))
              pivot column pivotValue rfl shapeAColumn.below_zero
              0 (A pivot column)
            · exact dvd_refl _
            · exact dvd_zero _
            · exact Submodule.mem_sup_left differenceMem
            · intro currentColumn currentBefore
              change A row currentColumn - H row currentColumn = 0
              rw [ih currentColumn.val currentBefore currentColumn.isLt row]
              simp
          have modEq : A row column ≡ H row column [ZMOD A pivot column] := by
            rw [Int.modEq_iff_dvd]
            have negDivides : A pivot column ∣
                -((A.row row - H.row row) column) :=
              dvd_neg.mpr differenceDvd
            simpa using negDivides
          calc
            A row column = A row column % A pivot column :=
              shapeAColumn.above_reduced row rowBefore
            _ = H row column % A pivot column := modEq
            _ = H row column % H pivot column := by rw [pivotEq]
            _ = H row column :=
              (shapeHColumn.above_reduced row rowBefore).symm
        · by_cases rowEq : row = pivot
          · subst row
            exact pivotEq
          · have pivotBefore : pivot < row := by
              exact lt_of_le_of_ne (not_lt.mp rowBefore) (Ne.symm rowEq)
            rw [shapeAColumn.below_zero row pivotBefore,
              shapeHColumn.below_zero row pivotBefore]
  ext row column
  exact columnEq column.val column.isLt row

structure ReferenceInvariant {m n : Nat} (columns_le_rows : n ≤ m)
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (state : RawModularRun m n) (processed : Nat) : Prop where
  shape : RunInvariant columns_le_rows state processed
  lattice_eq :
    augmentedRowSpan state.candidate state.finalModulus processed = rowSpan H
  determinant_dvd :
    (suffixSquare H columns_le_rows processed).det ∣ state.finalModulus

theorem stage_referenceRunInvariant {m n : Nat}
    (columns_le_rows : n ≤ m)
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (referenceShape : ProcessedHermiteShape columns_le_rows H n)
    (state : RawModularRun m n) (processed : Nat) (column : Fin n)
    (columnValue : column.val = processed)
    (invariant :
      ReferenceInvariant columns_le_rows H state processed) :
    ReferenceInvariant columns_le_rows H
      (Internal.stage columns_le_rows state column) (processed + 1) := by
  subst processed
  have stageSemantic := stage_referenceInvariant columns_le_rows state
    column invariant.shape.prefix_zero invariant.shape.processed_shape
    invariant.shape.modulus_positive H referenceShape
    invariant.lattice_eq invariant.determinant_dvd
  exact
    { shape := Internal.stage_runInvariant columns_le_rows state column.val
        column rfl invariant.shape
      lattice_eq := stageSemantic.1
      determinant_dvd := stageSemantic.2 }

theorem runColumns_referenceInvariant {m n : Nat}
    (columns_le_rows : n ≤ m)
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (referenceShape : ProcessedHermiteShape columns_le_rows H n)
    (columns : List (Fin n)) (state : RawModularRun m n)
    (processed : Nat) (consecutive : ConsecutiveFrom processed columns)
    (invariant :
      ReferenceInvariant columns_le_rows H state processed) :
    ReferenceInvariant columns_le_rows H
      (Internal.runColumns columns_le_rows columns state)
      (processed + columns.length) := by
  induction consecutive generalizing state with
  | nil start => simpa [Internal.runColumns] using invariant
  | cons start column tail columnValue tailConsecutive ih =>
      have nextInvariant := stage_referenceRunInvariant
        columns_le_rows H referenceShape state start column columnValue invariant
      have finalInvariant := ih
        (Internal.stage columns_le_rows state column) nextInvariant
      simpa [Internal.runColumns, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using finalInvariant

theorem suffixModule_at_width_eq_bot {n : Nat} (modulus : Int) :
    suffixModule (n := n) modulus n =
      (⊥ : Submodule Int (Fin n → Int)) := by
  apply le_antisymm
  · rw [suffixModule, Submodule.span_le]
    rintro _ ⟨column, rfl⟩
    exact (Nat.not_lt_of_ge column.2 column.1.isLt).elim
  · exact bot_le

public theorem runWithDeterminantWitness_candidate_eq_reference {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) :
    (runWithDeterminantWitness A fullRank witness).candidate =
      (hermiteNormalFormFin A).H := by
  let columns_le_rows := fullRank.columns_le_rows
  let reference := hermiteNormalFormFin A
  let initial : RawModularRun m n :=
    { candidate := A
      finalModulus := witness.modulus
      stages := []
      operations := {} }
  have referenceSpec := hnf_fullColumnShape reference.H columns_le_rows
    reference.isHermite
    (cols_linearIndependent_of_rank_eq_width _
      (reference_rank_eq_width A fullRank))
  have referenceShape :
      ProcessedHermiteShape columns_le_rows reference.H n :=
    fun column _ => referenceSpec.2 column
  have referenceSpan : rowSpan reference.H = rowSpan A := by
    calc
      rowSpan reference.H = rowSpan (reference.U * A) := by
        rw [reference.equation]
      _ = rowSpan A := rowSpan_mul_eq reference.U_cert A
  have initialShape : RunInvariant columns_le_rows initial 0 :=
    { prefix_zero := by
        intro _ _ column before
        omega
      processed_shape := by
        intro _ before
        omega
      modulus_positive := witness.positive }
  have initialInvariant :
      ReferenceInvariant columns_le_rows reference.H initial 0 :=
    { shape := initialShape
      lattice_eq := by
        calc
          augmentedRowSpan initial.candidate initial.finalModulus 0 =
              rowSpan A := by
            exact determinantModulus_augmentedRowSpan_eq A fullRank witness 0
          _ = rowSpan reference.H := referenceSpan.symm
      determinant_dvd := by
        exact reference_initialDet_dvd_modulus A fullRank witness }
  have finalInvariant := runColumns_referenceInvariant
    columns_le_rows reference.H referenceShape (List.finRange n) initial 0
    (ConsecutiveFrom.finRange n) initialInvariant
  have lengthEq : (List.finRange n).length = n := List.length_finRange
  let final := Internal.runColumns columns_le_rows (List.finRange n) initial
  have finalShape : ProcessedHermiteShape columns_le_rows final.candidate n := by
    simpa [final, lengthEq] using finalInvariant.shape.processed_shape
  have finalSpan : rowSpan final.candidate = rowSpan reference.H := by
    have lattice := finalInvariant.lattice_eq
    rw [lengthEq] at lattice
    simpa [final, augmentedRowSpan, suffixModule_at_width_eq_bot] using lattice
  have finalEq : final.candidate = reference.H :=
    fullColumnShape_unique_of_rowSpan_eq columns_le_rows
      final.candidate reference.H finalShape referenceShape finalSpan
  simpa [runWithDeterminantWitness, runRaw, final, initial,
    columns_le_rows, reference] using finalEq

end NormalForms.Research.ModularHNF
