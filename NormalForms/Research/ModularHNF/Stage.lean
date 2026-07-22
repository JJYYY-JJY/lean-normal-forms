/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Pivot
import all NormalForms.Research.ModularHNF.Pivot

/-!
# One complete modular-HNF stage

This file composes the executable below-pivot, pivot-normalization, and
above-pivot loops.  Its shape theorem is independent of the determinant
contract: every stage over a positive live modulus creates one positive,
normalized diagonal pivot, zeros everything below it, canonically reduces
everything above it, advances the zero prefix, and keeps the next modulus
positive.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms

/-- The local HNF obligations established at one diagonal position. -/
structure ColumnHermiteShape {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) : Prop where
  pivot_positive : 0 < A pivot column
  pivot_normalized : A pivot column = normalize (A pivot column)
  below_zero : ∀ row, pivot < row → A row column = 0
  above_reduced : ∀ row, row < pivot →
    A row column = A row column % A pivot column

namespace ColumnHermiteShape

theorem of_column_eq {m n : Nat}
    {A B : _root_.Matrix (Fin m) (Fin n) Int}
    {pivot : Fin m} {column : Fin n}
    (shape : ColumnHermiteShape A pivot column)
    (columnEq : ∀ row, B row column = A row column) :
    ColumnHermiteShape B pivot column where
  pivot_positive := by
    rw [columnEq pivot]
    exact shape.pivot_positive
  pivot_normalized := by
    rw [columnEq pivot]
    exact shape.pivot_normalized
  below_zero := by
    intro row pivotBeforeRow
    rw [columnEq row]
    exact shape.below_zero row pivotBeforeRow
  above_reduced := by
    intro row rowBeforePivot
    rw [columnEq row, columnEq pivot]
    exact shape.above_reduced row rowBeforePivot

end ColumnHermiteShape

namespace Internal

theorem stage_candidate_apply_before {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column currentColumn : Fin n) (before : currentColumn < column)
    (row : Fin m) :
    (stage columns_le_rows state column).candidate row currentColumn =
      state.candidate row currentColumn := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := reduceBelow pivot column modulus (List.finRange m) prepared
  let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
  let scaled := scalePivotSuffix below.1 pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  let reduced := reduceAbove pivot column (List.finRange m).reverse restored
  change reduced row currentColumn = state.candidate row currentColumn
  have currentNe : currentColumn ≠ column := before.ne
  have preparedBefore :
      prepared row currentColumn = state.candidate row currentColumn := by
    by_cases pivotZero : state.candidate pivot column = 0
    · rw [show prepared = setEntry state.candidate pivot column modulus by
        simp [prepared, pivotZero]]
      by_cases rowEq : row = pivot
      · subst row
        exact setEntry_apply_of_column_ne state.candidate pivot column
          currentColumn modulus currentNe
      · exact setEntry_apply_of_row_ne state.candidate pivot row column
          currentColumn modulus rowEq
    · rw [show prepared = state.candidate by simp [prepared, pivotZero]]
  have belowBefore : below.1 row currentColumn = prepared row currentColumn :=
    reduceBelow_apply_before pivot row column currentColumn modulus before
      (List.finRange m) prepared
  have scaledBefore : scaled row currentColumn = below.1 row currentColumn := by
    exact scalePivotSuffix_apply_before below.1 pivot row column currentColumn
      gcdData.leftCoeff modulus before
  have restoredBefore : restored row currentColumn = scaled row currentColumn := by
    by_cases scaledZero : scaled pivot column = 0
    · rw [show restored = setEntry scaled pivot column modulus by
        simp [restored, scaledZero]]
      by_cases rowEq : row = pivot
      · subst row
        exact setEntry_apply_of_column_ne scaled pivot column currentColumn
          modulus currentNe
      · exact setEntry_apply_of_row_ne scaled pivot row column currentColumn
          modulus rowEq
    · rw [show restored = scaled by simp [restored, scaledZero]]
  calc
    reduced row currentColumn = restored row currentColumn :=
      reduceAbove_apply_before pivot row column currentColumn before
        (List.finRange m).reverse restored
    _ = scaled row currentColumn := restoredBefore
    _ = below.1 row currentColumn := scaledBefore
    _ = prepared row currentColumn := belowBefore
    _ = state.candidate row currentColumn := preparedBefore

theorem stage_beforeScale_augmentedRowSpan {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column : Fin n) (prefixZero : PrefixRowsZero state.candidate column.val) :
    let pivot : Fin m := Fin.castLE columns_le_rows column
    let modulus := state.finalModulus
    let prepared :=
      if state.candidate pivot column = 0 then
        setEntry state.candidate pivot column modulus
      else
        state.candidate
    let below := reduceBelow pivot column modulus (List.finRange m) prepared
    augmentedRowSpan below.1 modulus column.val =
      augmentedRowSpan state.candidate modulus column.val := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := reduceBelow pivot column modulus (List.finRange m) prepared
  have preparedPrefix : PrefixRowsZero prepared column.val := by
    by_cases pivotZero : state.candidate pivot column = 0
    · rw [show prepared = setEntry state.candidate pivot column modulus by
        simp [prepared, pivotZero]]
      exact setEntry_prefixRowsZero state.candidate pivot column modulus prefixZero
    · rw [show prepared = state.candidate by simp [prepared, pivotZero]]
      exact prefixZero
  have preparedSpan :
      augmentedRowSpan prepared modulus column.val =
        augmentedRowSpan state.candidate modulus column.val := by
    by_cases pivotZero : state.candidate pivot column = 0
    · rw [show prepared = setEntry state.candidate pivot column modulus by
        simp [prepared, pivotZero]]
      exact setEntry_augmentedRowSpan_of_zero state.candidate pivot column
        modulus pivotZero
    · rw [show prepared = state.candidate by simp [prepared, pivotZero]]
  have belowSpan :
      augmentedRowSpan below.1 modulus column.val =
        augmentedRowSpan prepared modulus column.val := by
    exact reduceBelow_augmentedRowSpan pivot column modulus (List.finRange m)
      prepared (by simp [pivot]) preparedPrefix
  exact belowSpan.trans preparedSpan

/-- A stage advances the augmented lattice once the next implicit suffix is semantically valid. -/
theorem stage_augmentedRowSpan_eq_next {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column : Fin n) (modulusPositive : 0 < state.finalModulus)
    (prefixZero : PrefixRowsZero state.candidate column.val)
    (nextSuffix :
      let pivot : Fin m := Fin.castLE columns_le_rows column
      let modulus := state.finalModulus
      let prepared :=
        if state.candidate pivot column = 0 then
          setEntry state.candidate pivot column modulus
        else
          state.candidate
      let below := reduceBelow pivot column modulus (List.finRange m) prepared
      let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
      suffixModule (modulus / gcdData.gcd) (column.val + 1) ≤
        augmentedRowSpan state.candidate modulus column.val) :
    augmentedRowSpan
        (stage columns_le_rows state column).candidate
        (stage columns_le_rows state column).finalModulus
        (column.val + 1) =
      augmentedRowSpan state.candidate state.finalModulus column.val := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := reduceBelow pivot column modulus (List.finRange m) prepared
  let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
  let scaled := scalePivotSuffix below.1 pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  let reduced := reduceAbove pivot column (List.finRange m).reverse restored
  have preparedPrefix : PrefixRowsZero prepared column.val := by
    by_cases pivotZero : state.candidate pivot column = 0
    · rw [show prepared = setEntry state.candidate pivot column modulus by
        simp [prepared, pivotZero]]
      exact setEntry_prefixRowsZero state.candidate pivot column modulus prefixZero
    · rw [show prepared = state.candidate by simp [prepared, pivotZero]]
      exact prefixZero
  have belowPrefix : PrefixRowsZero below.1 column.val :=
    reduceBelow_prefixRowsZero pivot column modulus (List.finRange m)
      prepared preparedPrefix
  have beforeSpan :
      augmentedRowSpan below.1 modulus column.val =
        augmentedRowSpan state.candidate modulus column.val := by
    simpa [pivot, modulus, prepared, below] using
      (stage_beforeScale_augmentedRowSpan columns_le_rows state column prefixZero)
  have nextSuffixBelow :
      suffixModule (modulus / gcdData.gcd) (column.val + 1) ≤
        augmentedRowSpan below.1 modulus column.val := by
    rw [beforeSpan]
    exact nextSuffix
  have pivotSpan :
      augmentedRowSpan restored (modulus / gcdData.gcd) (column.val + 1) =
        augmentedRowSpan below.1 modulus column.val := by
    simpa [gcdData, scaled, restored] using
      (scaleAndRestore_augmentedRowSpan_eq_next below.1 pivot column modulus
        (by simpa [modulus] using modulusPositive)
        (by simp [pivot]) belowPrefix nextSuffixBelow)
  have restoredPrefix : PrefixRowsZero restored column.val := by
    simpa [gcdData, scaled, restored] using
      (scaleAndRestore_prefixRowsZero below.1 pivot column modulus belowPrefix)
  have aboveSpan :
      augmentedRowSpan reduced (modulus / gcdData.gcd) (column.val + 1) =
        augmentedRowSpan restored (modulus / gcdData.gcd) (column.val + 1) := by
    exact reduceAbove_augmentedRowSpan_eq pivot column (List.finRange m).reverse
      restored (modulus / gcdData.gcd) (column.val + 1)
        (by simp [pivot]) restoredPrefix
  change augmentedRowSpan reduced (modulus / gcdData.gcd) (column.val + 1) =
    augmentedRowSpan state.candidate modulus column.val
  exact aboveSpan.trans (pivotSpan.trans beforeSpan)

/-- Full local shape and positivity contract for the executable `stage`. -/
theorem stage_shape {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column : Fin n) (modulusPositive : 0 < state.finalModulus)
    (prefixZero : PrefixRowsZero state.candidate column.val) :
    PrefixRowsZero
        (stage columns_le_rows state column).candidate (column.val + 1) ∧
      ColumnHermiteShape
        (stage columns_le_rows state column).candidate
        (Fin.castLE columns_le_rows column) column ∧
      0 < (stage columns_le_rows state column).finalModulus := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := reduceBelow pivot column modulus (List.finRange m) prepared
  let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
  let scaled := scalePivotSuffix below.1 pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  let reduced := reduceAbove pivot column (List.finRange m).reverse restored
  let next := stage columns_le_rows state column
  have nextCandidate : next.candidate = reduced := rfl
  have nextModulus : next.finalModulus = modulus / gcdData.gcd := rfl
  have preparedPrefix : PrefixRowsZero prepared column.val := by
    by_cases pivotZero : state.candidate pivot column = 0
    · rw [show prepared = setEntry state.candidate pivot column modulus by
        simp [prepared, pivotZero]]
      exact setEntry_prefixRowsZero state.candidate pivot column modulus prefixZero
    · rw [show prepared = state.candidate by simp [prepared, pivotZero]]
      exact prefixZero
  have belowPrefix : PrefixRowsZero below.1 column.val :=
    reduceBelow_prefixRowsZero pivot column modulus (List.finRange m)
      prepared preparedPrefix
  have belowZero : ∀ row, pivot < row → below.1 row column = 0 :=
    reduceBelow_finRange_column_zero pivot column modulus
      (by simpa [modulus] using modulusPositive) prepared
  have restoredPrefix : PrefixRowsZero restored column.val := by
    exact scaleAndRestore_prefixRowsZero below.1 pivot column modulus belowPrefix
  have restoredPivot : restored pivot column = gcdData.gcd := by
    simpa [gcdData] using
      (scaleAndRestore_pivot_column below.1 pivot column modulus
        (by simpa [modulus] using modulusPositive))
  have restoredBelow : ∀ row, pivot < row → restored row column = 0 := by
    intro row pivotBeforeRow
    calc
      restored row column = below.1 row column := by
        simpa [gcdData] using
          (scaleAndRestore_apply_of_row_ne below.1 pivot row
            pivotBeforeRow.ne' column column modulus)
      _ = 0 := belowZero row pivotBeforeRow
  have reducedPrefix : PrefixRowsZero reduced column.val := by
    exact reduceAbove_prefixRowsZero pivot column (List.finRange m).reverse
      restored restoredPrefix
  have reducedPivot : reduced pivot column = gcdData.gcd := by
    calc
      reduced pivot column = restored pivot column :=
        reduceAbove_pivot_apply pivot column column (List.finRange m).reverse restored
      _ = gcdData.gcd := restoredPivot
  have reducedBelow : ∀ row, pivot < row → reduced row column = 0 := by
    intro row pivotBeforeRow
    calc
      reduced row column = restored row column :=
        reduceAbove_apply_of_below pivot row pivotBeforeRow column column
          (List.finRange m).reverse restored
      _ = 0 := restoredBelow row pivotBeforeRow
  have reducedAbove : ∀ row, row < pivot →
      reduced row column = reduced row column % reduced pivot column := by
    intro row rowBeforePivot
    have reduction := reduceAbove_finRange_column_eq_mod pivot column restored
      row rowBeforePivot
    have reduction' :
        reduced row column = restored row column % restored pivot column :=
      reduction
    calc
      reduced row column = restored row column % restored pivot column := reduction'
      _ = (restored row column % restored pivot column) %
            restored pivot column := (Int.emod_emod _ _).symm
      _ = reduced row column % reduced pivot column := by
        rw [reduction', reducedPivot, restoredPivot]
  have reducedPrefixNext : PrefixRowsZero reduced (column.val + 1) := by
    intro row rowAfter currentColumn currentBefore
    by_cases strictlyBefore : currentColumn.val < column.val
    · exact reducedPrefix row (by omega) currentColumn strictlyBefore
    · have currentEq : currentColumn = column := by
        apply Fin.ext
        omega
      subst currentColumn
      apply reducedBelow row
      change pivot.val < row.val
      have pivotValue : pivot.val = column.val := by simp [pivot]
      omega
  have gcdPositive : 0 < gcdData.gcd := by
    simpa [gcdData, modulus] using
      (pivotGcd_positive (value := below.1 pivot column) modulusPositive)
  have reducedNormalized :
      reduced pivot column = normalize (reduced pivot column) := by
    simpa [reducedPivot, gcdData] using
      (ComputableEuclideanOps.xgcd_gcd_normalized
        (below.1 pivot column) modulus)
  have nextModulusPositive : 0 < modulus / gcdData.gcd := by
    simpa [gcdData, modulus] using
      (pivotModulusQuotient_positive
        (value := below.1 pivot column) modulusPositive)
  constructor
  · rw [show (stage columns_le_rows state column).candidate = reduced from
      nextCandidate]
    exact reducedPrefixNext
  · constructor
    · rw [show (stage columns_le_rows state column).candidate = reduced from
        nextCandidate]
      exact
        { pivot_positive := by
            change 0 < reduced pivot column
            rw [reducedPivot]
            exact gcdPositive
          pivot_normalized := reducedNormalized
          below_zero := reducedBelow
          above_reduced := reducedAbove }
    · rw [show (stage columns_le_rows state column).finalModulus =
        modulus / gcdData.gcd from nextModulus]
      exact nextModulusPositive

end Internal

end NormalForms.Research.ModularHNF
