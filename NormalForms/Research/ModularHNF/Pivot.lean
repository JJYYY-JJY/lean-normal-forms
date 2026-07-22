/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Above
import all NormalForms.Research.ModularHNF.Above

/-!
# Pivot normalization in modular HNF

The second extended-gcd call combines the reduced pivot with the live positive
modulus.  Scaling modulo that modulus yields the normalized gcd, except when
the gcd equals the modulus and hence has representative zero; the executable
restoration branch then writes the modulus itself.  Thus the restored pivot is
always the positive normalized gcd.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms

namespace Internal

open scoped BigOperators Matrix

theorem setEntry_prefixRowsZero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (column : Fin n) (value : Int)
    (prefixZero : PrefixRowsZero A column.val) :
    PrefixRowsZero (setEntry A row column value) column.val := by
  intro currentRow rowAfter currentColumn currentBefore
  have columnNe : currentColumn ≠ column := by
    intro equality
    subst currentColumn
    exact Nat.lt_irrefl _ currentBefore
  by_cases rowEq : currentRow = row
  · subst currentRow
    rw [setEntry_apply_of_column_ne A row column currentColumn value columnNe]
    exact prefixZero row rowAfter currentColumn currentBefore
  · rw [setEntry_apply_of_row_ne A row currentRow column currentColumn value rowEq]
    exact prefixZero currentRow rowAfter currentColumn currentBefore

theorem scalePivotSuffix_apply_before {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot row : Fin m) (column currentColumn : Fin n)
    (coefficient modulus : Int) (before : currentColumn < column) :
    scalePivotSuffix A pivot column coefficient modulus row currentColumn =
      A row currentColumn := by
  have notAfter : ¬ column ≤ currentColumn := not_le_of_gt before
  simp [scalePivotSuffix, notAfter]

theorem scalePivotSuffix_prefixRowsZero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (coefficient modulus : Int)
    (prefixZero : PrefixRowsZero A column.val) :
    PrefixRowsZero
      (scalePivotSuffix A pivot column coefficient modulus) column.val := by
  intro row rowAfter currentColumn currentBefore
  rw [scalePivotSuffix_apply_before A pivot row column currentColumn
    coefficient modulus currentBefore]
  exact prefixZero row rowAfter currentColumn currentBefore

theorem scalePivotSuffix_apply_of_row_ne {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot row : Fin m) (rowNotPivot : row ≠ pivot)
    (column currentColumn : Fin n) (coefficient modulus : Int) :
    scalePivotSuffix A pivot column coefficient modulus row currentColumn =
      A row currentColumn := by
  simp [scalePivotSuffix, rowNotPivot]

theorem scalePivotSuffix_pivot_column {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (coefficient modulus : Int) :
    scalePivotSuffix A pivot column coefficient modulus pivot column =
      (coefficient * A pivot column) % modulus := by
  simp [scalePivotSuffix]

theorem pivotModEqGcd {value modulus : Int} :
    let gcdData := ComputableEuclideanOps.xgcd value modulus
    (gcdData.leftCoeff * value) % modulus = gcdData.gcd % modulus := by
  let gcdData := ComputableEuclideanOps.xgcd value modulus
  have difference :
      modulus ∣ gcdData.gcd - gcdData.leftCoeff * value := by
    refine ⟨gcdData.rightCoeff, ?_⟩
    have bezout := ComputableEuclideanOps.xgcd_bezout value modulus
    dsimp [gcdData] at bezout ⊢
    rw [← bezout]
    ring
  exact Int.ModEq.eq ((Int.modEq_iff_dvd).2 difference)

theorem pivotGcd_nonnegative (value modulus : Int) :
    0 ≤ (ComputableEuclideanOps.xgcd value modulus).gcd := by
  apply Int.nonneg_of_normalize_eq_self
  exact (ComputableEuclideanOps.xgcd_gcd_normalized value modulus).symm

theorem pivotGcd_positive {value modulus : Int} (modulusPositive : 0 < modulus) :
    0 < (ComputableEuclideanOps.xgcd value modulus).gcd := by
  have nonzero : (ComputableEuclideanOps.xgcd value modulus).gcd ≠ 0 := by
    intro gcdZero
    have bothZero :=
      (ComputableEuclideanOps.xgcd_gcd_eq_zero_iff value modulus).mp gcdZero
    exact (ne_of_gt modulusPositive) bothZero.2
  exact lt_of_le_of_ne (pivotGcd_nonnegative value modulus) (Ne.symm nonzero)

theorem pivotGcd_le_modulus {value modulus : Int}
    (modulusPositive : 0 < modulus) :
    (ComputableEuclideanOps.xgcd value modulus).gcd ≤ modulus :=
  Int.le_of_dvd modulusPositive
    (ComputableEuclideanOps.xgcd_gcd_dvd_right value modulus)

theorem pivotModulusQuotient_positive {value modulus : Int}
    (modulusPositive : 0 < modulus) :
    0 < modulus / (ComputableEuclideanOps.xgcd value modulus).gcd := by
  let gcdValue := (ComputableEuclideanOps.xgcd value modulus).gcd
  have gcdPositive : 0 < gcdValue := by
    simpa [gcdValue] using
      (pivotGcd_positive (value := value) modulusPositive)
  have gcdDivides : gcdValue ∣ modulus := by
    simpa [gcdValue] using
      (ComputableEuclideanOps.xgcd_gcd_dvd_right value modulus)
  have quotientNonnegative : 0 ≤ modulus / gcdValue :=
    Int.ediv_nonneg (le_of_lt modulusPositive) (le_of_lt gcdPositive)
  have quotientNonzero : modulus / gcdValue ≠ 0 := by
    intro quotientZero
    have exactProduct := Int.ediv_mul_cancel gcdDivides
    rw [quotientZero, zero_mul] at exactProduct
    exact (ne_of_gt modulusPositive) exactProduct.symm
  exact lt_of_le_of_ne quotientNonnegative (Ne.symm quotientNonzero)

/-- The scale-and-restore fragment writes the positive normalized gcd at the pivot. -/
theorem scaleAndRestore_pivot_column {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (modulusPositive : 0 < modulus) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    restored pivot column = gcdData.gcd := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  change restored pivot column = gcdData.gcd
  have gcdPositive : 0 < gcdData.gcd := by
    simpa [gcdData] using
      (pivotGcd_positive (value := A pivot column) modulusPositive)
  have gcdNonnegative : 0 ≤ gcdData.gcd := le_of_lt gcdPositive
  have gcdLe : gcdData.gcd ≤ modulus := by
    simpa [gcdData] using
      (pivotGcd_le_modulus (value := A pivot column) modulusPositive)
  have scaledEq : scaled pivot column = gcdData.gcd % modulus := by
    change scalePivotSuffix A pivot column gcdData.leftCoeff modulus
        pivot column = gcdData.gcd % modulus
    rw [scalePivotSuffix_pivot_column]
    simpa [gcdData] using
      (pivotModEqGcd (value := A pivot column) (modulus := modulus))
  by_cases gcdLt : gcdData.gcd < modulus
  · have gcdMod : gcdData.gcd % modulus = gcdData.gcd :=
      Int.emod_eq_of_lt gcdNonnegative gcdLt
    have scaledNonzero : scaled pivot column ≠ 0 := by
      rw [scaledEq, gcdMod]
      exact ne_of_gt gcdPositive
    rw [show restored = scaled by simp [restored, scaledNonzero]]
    exact scaledEq.trans gcdMod
  · have gcdEq : gcdData.gcd = modulus :=
      le_antisymm gcdLe (le_of_not_gt gcdLt)
    have scaledZero : scaled pivot column = 0 := by
      rw [scaledEq, gcdEq]
      simp
    rw [show restored = setEntry scaled pivot column modulus by
      simp [restored, scaledZero]]
    simp [gcdEq]

theorem scaleAndRestore_prefixRowsZero {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (prefixZero : PrefixRowsZero A column.val) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    PrefixRowsZero restored column.val := by
  dsimp only
  split
  · exact setEntry_prefixRowsZero _ pivot column modulus
      (scalePivotSuffix_prefixRowsZero A pivot column _ modulus prefixZero)
  · exact scalePivotSuffix_prefixRowsZero A pivot column _ modulus prefixZero

theorem scaleAndRestore_apply_of_row_ne {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot row : Fin m) (rowNotPivot : row ≠ pivot)
    (column currentColumn : Fin n) (modulus : Int) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    restored row currentColumn = A row currentColumn := by
  dsimp only
  split
  · rw [setEntry_apply_of_row_ne _ pivot row column currentColumn modulus
      rowNotPivot]
    exact scalePivotSuffix_apply_of_row_ne A pivot row rowNotPivot
      column currentColumn _ modulus
  · exact scalePivotSuffix_apply_of_row_ne A pivot row rowNotPivot
      column currentColumn _ modulus

/-- Every updated pivot entry is congruent to the scaled old entry modulo the live modulus. -/
theorem scaleAndRestore_pivot_dvd_difference {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column currentColumn : Fin n) (modulus : Int)
    (after : column ≤ currentColumn) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    modulus ∣ restored pivot currentColumn -
      gcdData.leftCoeff * A pivot currentColumn := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  have scaledApply :
      scaled pivot currentColumn =
        (gcdData.leftCoeff * A pivot currentColumn) % modulus := by
    simp [scaled, scalePivotSuffix, after]
  change modulus ∣ restored pivot currentColumn -
    gcdData.leftCoeff * A pivot currentColumn
  by_cases scaledZero : scaled pivot column = 0
  · rw [show restored = setEntry scaled pivot column modulus by
      simp [restored, scaledZero]]
    by_cases currentEq : currentColumn = column
    · subst currentColumn
      rw [setEntry_apply_same]
      have rawModZero :
          (gcdData.leftCoeff * A pivot column) % modulus = 0 := by
        simpa [scaledApply] using scaledZero
      have rawDivides :
          modulus ∣ gcdData.leftCoeff * A pivot column :=
        Int.dvd_of_emod_eq_zero rawModZero
      exact dvd_sub (dvd_refl modulus) rawDivides
    · rw [setEntry_apply_of_column_ne scaled pivot column currentColumn
        modulus currentEq]
      exact Int.dvd_sub_self_of_emod_eq scaledApply.symm
  · rw [show restored = scaled by simp [restored, scaledZero]]
    exact Int.dvd_sub_self_of_emod_eq scaledApply.symm

/-- The restored pivot row is congruent to the Bézout-scaled old row modulo the live suffix. -/
theorem scaleAndRestore_pivot_difference_mem {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (pivotPrefixZero : ∀ currentColumn, currentColumn < column →
      A pivot currentColumn = 0) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    restored.row pivot - gcdData.leftCoeff • A.row pivot ∈
      suffixModule modulus column.val := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  apply mem_suffixModule_of_coordinates
  · intro currentColumn before
    have currentBefore : currentColumn < column := before
    have oldZero := pivotPrefixZero currentColumn currentBefore
    have scaledBefore : scaled pivot currentColumn = A pivot currentColumn :=
      scalePivotSuffix_apply_before A pivot pivot column currentColumn
        gcdData.leftCoeff modulus currentBefore
    have restoredBefore : restored pivot currentColumn = scaled pivot currentColumn := by
      by_cases scaledZero : scaled pivot column = 0
      · rw [show restored = setEntry scaled pivot column modulus by
          simp [restored, scaledZero]]
        exact setEntry_apply_of_column_ne scaled pivot column currentColumn
          modulus currentBefore.ne
      · rw [show restored = scaled by simp [restored, scaledZero]]
    change restored pivot currentColumn -
        gcdData.leftCoeff * A pivot currentColumn = 0
    rw [restoredBefore, scaledBefore, oldZero]
    simp
  · intro currentColumn after
    exact scaleAndRestore_pivot_dvd_difference A pivot column currentColumn
      modulus after

/-- Scaling and restoring cannot introduce rows outside the old augmented lattice. -/
theorem scaleAndRestore_rowSpan_le_augmented {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (pivotPrefixZero : ∀ currentColumn, currentColumn < column →
      A pivot currentColumn = 0) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    rowSpan restored ≤ augmentedRowSpan A modulus column.val := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
      else
        scaled
  change Submodule.span Int (Set.range restored.row) ≤
    augmentedRowSpan A modulus column.val
  rw [Submodule.span_le]
  rintro _ ⟨row, rfl⟩
  by_cases rowEq : row = pivot
  · subst row
    have differenceMem :
        restored.row pivot - gcdData.leftCoeff • A.row pivot ∈
          augmentedRowSpan A modulus column.val :=
      Submodule.mem_sup_right
        (scaleAndRestore_pivot_difference_mem A pivot column modulus
          pivotPrefixZero)
    have scaledMem : gcdData.leftCoeff • A.row pivot ∈
        augmentedRowSpan A modulus column.val :=
      Submodule.smul_mem _ _ (Submodule.mem_sup_left (row_mem_rowSpan A pivot))
    have equality : restored.row pivot =
        gcdData.leftCoeff • A.row pivot +
          (restored.row pivot - gcdData.leftCoeff • A.row pivot) := by
      module
    rw [equality]
    exact Submodule.add_mem _ scaledMem differenceMem
  · have rowEqOld : restored.row row = A.row row := by
      ext currentColumn
      exact scaleAndRestore_apply_of_row_ne A pivot row rowEq column
        currentColumn modulus
    rw [rowEqOld]
    exact Submodule.mem_sup_left (row_mem_rowSpan A row)

/-- Dividing the Bézout identity by its positive gcd gives coprime quotient coefficients. -/
theorem pivotBezoutQuotient_identity (value modulus : Int)
    (modulusPositive : 0 < modulus) :
    let gcdData := ComputableEuclideanOps.xgcd value modulus
    gcdData.leftCoeff * (value / gcdData.gcd) +
        gcdData.rightCoeff * (modulus / gcdData.gcd) = 1 := by
  let gcdData := ComputableEuclideanOps.xgcd value modulus
  have gcdNonzero : gcdData.gcd ≠ 0 := ne_of_gt
    (pivotGcd_positive (value := value) modulusPositive)
  have gcdDvdValue : gcdData.gcd ∣ value := by
    simpa [gcdData] using
      (ComputableEuclideanOps.xgcd_gcd_dvd_left value modulus)
  have gcdDvdModulus : gcdData.gcd ∣ modulus := by
    simpa [gcdData] using
      (ComputableEuclideanOps.xgcd_gcd_dvd_right value modulus)
  have valueExact : value / gcdData.gcd * gcdData.gcd = value :=
    Int.ediv_mul_cancel gcdDvdValue
  have modulusExact : modulus / gcdData.gcd * gcdData.gcd = modulus :=
    Int.ediv_mul_cancel gcdDvdModulus
  have bezout :
      gcdData.leftCoeff * value + gcdData.rightCoeff * modulus =
        gcdData.gcd := by
    simpa [gcdData, mul_comm] using
      (ComputableEuclideanOps.xgcd_bezout value modulus)
  apply mul_right_cancel₀ gcdNonzero
  calc
    (gcdData.leftCoeff * (value / gcdData.gcd) +
          gcdData.rightCoeff * (modulus / gcdData.gcd)) * gcdData.gcd =
        gcdData.leftCoeff * value + gcdData.rightCoeff * modulus := by
          rw [add_mul, mul_assoc, valueExact, mul_assoc, modulusExact]
    _ = gcdData.gcd := bezout
    _ = 1 * gcdData.gcd := by simp

/-- The old pivot row is recoverable from the restored row and the next suffix basis. -/
theorem scaleAndRestore_oldPivot_difference_mem_nextSuffix {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (modulusPositive : 0 < modulus)
    (pivotValue : pivot.val = column.val)
    (prefixZero : PrefixRowsZero A column.val) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    A.row pivot - (A pivot column / gcdData.gcd) • restored.row pivot ∈
      suffixModule (modulus / gcdData.gcd) (column.val + 1) := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  let xQuot := A pivot column / gcdData.gcd
  let nextModulus := modulus / gcdData.gcd
  have gcdDvdValue : gcdData.gcd ∣ A pivot column := by
    simpa [gcdData] using
      (ComputableEuclideanOps.xgcd_gcd_dvd_left (A pivot column) modulus)
  have gcdDvdModulus : gcdData.gcd ∣ modulus := by
    simpa [gcdData] using
      (ComputableEuclideanOps.xgcd_gcd_dvd_right (A pivot column) modulus)
  have valueExact : xQuot * gcdData.gcd = A pivot column := by
    simpa [xQuot] using Int.ediv_mul_cancel gcdDvdValue
  have modulusExact : nextModulus * gcdData.gcd = modulus := by
    simpa [nextModulus] using Int.ediv_mul_cancel gcdDvdModulus
  have quotientIdentity :
      gcdData.leftCoeff * xQuot +
          gcdData.rightCoeff * nextModulus = 1 := by
    simpa [gcdData, xQuot, nextModulus] using
      pivotBezoutQuotient_identity (A pivot column) modulus modulusPositive
  have restoredPivot : restored pivot column = gcdData.gcd := by
    simpa [gcdData, scaled, restored] using
      (scaleAndRestore_pivot_column A pivot column modulus modulusPositive)
  have restoredPrefix : PrefixRowsZero restored column.val := by
    simpa [gcdData, scaled, restored] using
      (scaleAndRestore_prefixRowsZero A pivot column modulus prefixZero)
  apply mem_suffixModule_of_coordinates
  · intro currentColumn before
    by_cases strictlyBefore : currentColumn.val < column.val
    · have oldZero := prefixZero pivot (by omega) currentColumn strictlyBefore
      have newZero := restoredPrefix pivot (by omega) currentColumn strictlyBefore
      change A pivot currentColumn - xQuot * restored pivot currentColumn = 0
      rw [oldZero, newZero]
      simp
    · have currentEq : currentColumn = column := by
        apply Fin.ext
        omega
      subst currentColumn
      change A pivot column - xQuot * restored pivot column = 0
      rw [restoredPivot, valueExact]
      simp
  · intro currentColumn after
    have columnBefore : column ≤ currentColumn := by
      change column.val ≤ currentColumn.val
      omega
    have modulusDifference :
        modulus ∣ restored pivot currentColumn -
          gcdData.leftCoeff * A pivot currentColumn :=
      scaleAndRestore_pivot_dvd_difference A pivot column currentColumn
        modulus columnBefore
    have nextDvdModulus : nextModulus ∣ modulus :=
      ⟨gcdData.gcd, modulusExact.symm⟩
    have nextDvdDifference :
        nextModulus ∣ restored pivot currentColumn -
          gcdData.leftCoeff * A pivot currentColumn :=
      dvd_trans nextDvdModulus modulusDifference
    have firstTerm :
        nextModulus ∣
          (1 - xQuot * gcdData.leftCoeff) * A pivot currentColumn := by
      refine ⟨gcdData.rightCoeff * A pivot currentColumn, ?_⟩
      have identity :
          1 - xQuot * gcdData.leftCoeff =
            gcdData.rightCoeff * nextModulus := by
        nlinarith [quotientIdentity]
      rw [identity]
      ring
    have secondTerm :
        nextModulus ∣ xQuot *
          (restored pivot currentColumn -
            gcdData.leftCoeff * A pivot currentColumn) :=
      dvd_mul_of_dvd_right nextDvdDifference xQuot
    change nextModulus ∣
      A pivot currentColumn - xQuot * restored pivot currentColumn
    have decomposition :
        A pivot currentColumn - xQuot * restored pivot currentColumn =
          (1 - xQuot * gcdData.leftCoeff) * A pivot currentColumn -
            xQuot * (restored pivot currentColumn -
              gcdData.leftCoeff * A pivot currentColumn) := by
      ring
    rw [decomposition]
    exact dvd_sub firstTerm secondTerm

/-- The old augmented lattice is generated by the restored rows and the smaller next suffix. -/
theorem scaleAndRestore_old_augmented_le_next {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (modulusPositive : 0 < modulus)
    (pivotValue : pivot.val = column.val)
    (prefixZero : PrefixRowsZero A column.val) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    augmentedRowSpan A modulus column.val ≤
      augmentedRowSpan restored (modulus / gcdData.gcd) (column.val + 1) := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  let xQuot := A pivot column / gcdData.gcd
  let nextModulus := modulus / gcdData.gcd
  let nextLattice := augmentedRowSpan restored nextModulus (column.val + 1)
  have gcdDvdModulus : gcdData.gcd ∣ modulus := by
    simpa [gcdData] using
      (ComputableEuclideanOps.xgcd_gcd_dvd_right (A pivot column) modulus)
  have modulusExact : nextModulus * gcdData.gcd = modulus := by
    simpa [nextModulus] using Int.ediv_mul_cancel gcdDvdModulus
  have restoredPivot : restored pivot column = gcdData.gcd := by
    simpa [gcdData, scaled, restored] using
      (scaleAndRestore_pivot_column A pivot column modulus modulusPositive)
  have restoredPrefix : PrefixRowsZero restored column.val := by
    simpa [gcdData, scaled, restored] using
      (scaleAndRestore_prefixRowsZero A pivot column modulus prefixZero)
  have pivotDifference :
      A.row pivot - xQuot • restored.row pivot ∈
        suffixModule nextModulus (column.val + 1) := by
    simpa [gcdData, scaled, restored, xQuot, nextModulus] using
      (scaleAndRestore_oldPivot_difference_mem_nextSuffix A pivot column
        modulus modulusPositive pivotValue prefixZero)
  apply sup_le
  · change rowSpan A ≤ nextLattice
    rw [rowSpan, Submodule.span_le]
    rintro _ ⟨row, rfl⟩
    by_cases rowEq : row = pivot
    · subst row
      have scaledMem : xQuot • restored.row pivot ∈ nextLattice :=
        Submodule.smul_mem _ _
          (Submodule.mem_sup_left (row_mem_rowSpan restored pivot))
      have differenceMem :
          A.row pivot - xQuot • restored.row pivot ∈ nextLattice :=
        Submodule.mem_sup_right pivotDifference
      have equality : A.row pivot =
          xQuot • restored.row pivot +
            (A.row pivot - xQuot • restored.row pivot) := by
        module
      rw [equality]
      exact Submodule.add_mem _ scaledMem differenceMem
    · have rowEquality : A.row row = restored.row row := by
        ext currentColumn
        symm
        exact scaleAndRestore_apply_of_row_ne A pivot row rowEq column
          currentColumn modulus
      rw [rowEquality]
      exact Submodule.mem_sup_left (row_mem_rowSpan restored row)
  · change suffixModule modulus column.val ≤ nextLattice
    rw [suffixModule, Submodule.span_le]
    rintro _ ⟨sourceColumn, rfl⟩
    by_cases sourceAtPivot : sourceColumn.1.val = column.val
    · have sourceEq : sourceColumn.1 = column := by
        apply Fin.ext
        exact sourceAtPivot
      change modulus • Pi.single sourceColumn.1 (1 : Int) ∈ nextLattice
      rw [sourceEq]
      let pivotBasis : Fin n → Int := Pi.single column (1 : Int)
      change modulus • pivotBasis ∈ nextLattice
      have isolation :
          modulus • pivotBasis -
              nextModulus • restored.row pivot ∈
            suffixModule nextModulus (column.val + 1) := by
        apply mem_suffixModule_of_coordinates
        · intro currentColumn before
          by_cases strictlyBefore : currentColumn.val < column.val
          · have currentNe : currentColumn ≠ column := by
              intro equality
              subst currentColumn
              omega
            have newZero := restoredPrefix pivot (by omega)
              currentColumn strictlyBefore
            simp [pivotBasis, currentNe, newZero]
          · have currentEq : currentColumn = column := by
              apply Fin.ext
              omega
            subst currentColumn
            simp [pivotBasis, restoredPivot, modulusExact]
        · intro currentColumn _after
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          refine ⟨gcdData.gcd * pivotBasis currentColumn -
              restored pivot currentColumn, ?_⟩
          change modulus * pivotBasis currentColumn -
              nextModulus * restored pivot currentColumn =
            nextModulus *
              (gcdData.gcd * pivotBasis currentColumn -
                restored pivot currentColumn)
          rw [← modulusExact]
          ring
      have scaledPivotMem :
          nextModulus • restored.row pivot ∈ nextLattice :=
        Submodule.smul_mem _ _
          (Submodule.mem_sup_left (row_mem_rowSpan restored pivot))
      have isolationMem :
          modulus • pivotBasis -
              nextModulus • restored.row pivot ∈ nextLattice :=
        Submodule.mem_sup_right isolation
      have equality : modulus • pivotBasis =
          nextModulus • restored.row pivot +
            (modulus • pivotBasis -
              nextModulus • restored.row pivot) := by
        module
      rw [equality]
      exact Submodule.add_mem _ scaledPivotMem isolationMem
    · have sourceAfter : column.val + 1 ≤ sourceColumn.1.val := by
        omega
      have generator := suffixGenerator_mem nextModulus
        (⟨sourceColumn.1, sourceAfter⟩ : SuffixIndex n (column.val + 1))
      have scaledGenerator :=
        Submodule.smul_mem
          (suffixModule nextModulus (column.val + 1)) gcdData.gcd generator
      apply Submodule.mem_sup_right
      let sourceBasis : Fin n → Int := Pi.single sourceColumn.1 (1 : Int)
      have vectorEq :
          modulus • sourceBasis =
            gcdData.gcd •
              (nextModulus • sourceBasis) := by
        ext currentColumn
        change modulus * sourceBasis currentColumn =
          gcdData.gcd * (nextModulus * sourceBasis currentColumn)
        rw [← modulusExact]
        ring
      change modulus • sourceBasis ∈ suffixModule nextModulus (column.val + 1)
      rw [vectorEq]
      simpa [sourceBasis] using scaledGenerator

/-- If the next implicit suffix is valid in the old lattice, restoration cannot enlarge it. -/
theorem scaleAndRestore_next_augmented_le_old {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (pivotPrefixZero : ∀ currentColumn, currentColumn < column →
      A pivot currentColumn = 0)
    (nextSuffix :
      let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
      suffixModule (modulus / gcdData.gcd) (column.val + 1) ≤
        augmentedRowSpan A modulus column.val) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    augmentedRowSpan restored (modulus / gcdData.gcd) (column.val + 1) ≤
      augmentedRowSpan A modulus column.val := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  apply sup_le
  · exact scaleAndRestore_rowSpan_le_augmented A pivot column modulus
      pivotPrefixZero
  · exact nextSuffix

/-- Under the next-suffix containment, scale-and-restore advances the augmented lattice exactly. -/
theorem scaleAndRestore_augmentedRowSpan_eq_next {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (modulusPositive : 0 < modulus)
    (pivotValue : pivot.val = column.val)
    (prefixZero : PrefixRowsZero A column.val)
    (nextSuffix :
      let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
      suffixModule (modulus / gcdData.gcd) (column.val + 1) ≤
        augmentedRowSpan A modulus column.val) :
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
    let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
    let restored :=
      if scaled pivot column = 0 then
        setEntry scaled pivot column modulus
      else
        scaled
    augmentedRowSpan restored (modulus / gcdData.gcd) (column.val + 1) =
      augmentedRowSpan A modulus column.val := by
  let gcdData := ComputableEuclideanOps.xgcd (A pivot column) modulus
  let scaled := scalePivotSuffix A pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  apply le_antisymm
  · exact scaleAndRestore_next_augmented_le_old A pivot column modulus
      (fun currentColumn before =>
        prefixZero pivot (by omega) currentColumn before) nextSuffix
  · exact scaleAndRestore_old_augmented_le_next A pivot column modulus
      modulusPositive pivotValue prefixZero

end Internal

end NormalForms.Research.ModularHNF
