/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Correctness
import all NormalForms.Research.ModularHNF.Correctness
import all NormalForms.Research.ModularHNF.Algorithm
import all NormalForms.Research.ModularHNF.Pivot

/-!
# Coefficient bounds for modular HNF

The stored matrices of the DKT kernel admit a fully explicit intermediate
coefficient envelope.  Centered modular reductions remain within the live
modulus; an above-pivot row update maps an entry-height bound `B` to
`B + B * B`.  Composing that growth across every visited row and column gives
a conservative executable bound for every raw prefix.  The canonical final
matrix satisfies the sharper fact that every entry is bounded by the caller's
legal determinant modulus.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms.Matrix.Hermite

/-- Binary length of an integer magnitude; zero has length zero. -/
@[expose] public def integerBitLength (value : Int) : Nat :=
  Nat.size value.natAbs

/-- Largest absolute entry of a finite integer matrix. -/
@[expose] public def matrixHeight {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : Nat :=
  Finset.univ.sup fun row =>
    Finset.univ.sup fun column => (A row column).natAbs

/-- Binary length of the largest absolute matrix entry. -/
@[expose] public def matrixBitLength {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : Nat :=
  Nat.size (matrixHeight A)

public theorem entry_natAbs_le_matrixHeight {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (column : Fin n) :
    (A row column).natAbs ≤ matrixHeight A := by
  exact (Finset.le_sup
    (f := fun column => (A row column).natAbs)
    (Finset.mem_univ column)).trans
      (Finset.le_sup
        (f := fun row => Finset.univ.sup fun column =>
          (A row column).natAbs)
        (Finset.mem_univ row))

public theorem matrixHeight_le {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int} {bound : Nat}
    (hbound : ∀ row column, (A row column).natAbs ≤ bound) :
    matrixHeight A ≤ bound := by
  apply Finset.sup_le
  intro row _
  apply Finset.sup_le
  intro column _
  exact hbound row column

/-- Pointwise coefficient-height predicate for a finite integer matrix. -/
@[expose] public def EntriesBounded {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (bound : Nat) : Prop :=
  ∀ row column, (A row column).natAbs ≤ bound

namespace EntriesBounded

public theorem mono {m n : Nat} {A : _root_.Matrix (Fin m) (Fin n) Int}
    {smaller larger : Nat} (bounded : EntriesBounded A smaller)
    (le : smaller ≤ larger) : EntriesBounded A larger := by
  intro row column
  exact (bounded row column).trans le

end EntriesBounded

/-- Coarse height growth of one above-pivot row update. -/
@[expose] public def coefficientGrowth (bound : Nat) : Nat :=
  bound + bound * bound

/-- Iterate the one-row coefficient envelope a specified number of times. -/
@[expose] public def coefficientSteps : Nat → Nat → Nat
  | 0, bound => bound
  | steps + 1, bound => coefficientSteps steps (coefficientGrowth bound)

public theorem coefficientGrowth_mono {smaller larger : Nat}
    (le : smaller ≤ larger) :
    coefficientGrowth smaller ≤ coefficientGrowth larger := by
  unfold coefficientGrowth
  exact Nat.add_le_add le (Nat.mul_le_mul le le)

public theorem coefficientGrowth_le (bound : Nat) :
    bound ≤ coefficientGrowth bound := by
  simp [coefficientGrowth]

public theorem coefficientSteps_mono (steps : Nat) {smaller larger : Nat}
    (le : smaller ≤ larger) :
    coefficientSteps steps smaller ≤ coefficientSteps steps larger := by
  induction steps generalizing smaller larger with
  | zero => exact le
  | succ steps ih =>
      rw [coefficientSteps, coefficientSteps]
      exact ih (coefficientGrowth_mono le)

public theorem coefficientSteps_base_le (steps bound : Nat) :
    bound ≤ coefficientSteps steps bound := by
  induction steps generalizing bound with
  | zero => rfl
  | succ steps ih =>
      rw [coefficientSteps]
      exact (coefficientGrowth_le bound).trans (ih (coefficientGrowth bound))

public theorem coefficientSteps_add (first second bound : Nat) :
    coefficientSteps (first + second) bound =
      coefficientSteps second (coefficientSteps first bound) := by
  induction first generalizing bound with
  | zero => simp [coefficientSteps]
  | succ first ih =>
      rw [Nat.succ_add, coefficientSteps, coefficientSteps, ih]

namespace Internal

theorem emod_natAbs_le (value modulus : Int) (modulusPositive : 0 < modulus) :
    (value % modulus).natAbs ≤ modulus.natAbs := by
  have modulusNonzero := ne_of_gt modulusPositive
  have remainderNonnegative := Int.emod_nonneg value modulusNonzero
  have remainderLess := Int.emod_lt value modulusNonzero
  have remainderLessModulus : value % modulus < modulus := by
    simpa [Int.natAbs_of_nonneg (le_of_lt modulusPositive)] using
      remainderLess
  apply Int.ofNat_le.mp
  rw [Int.natAbs_of_nonneg remainderNonnegative,
    Int.natAbs_of_nonneg (le_of_lt modulusPositive)]
  exact le_of_lt remainderLessModulus

theorem centeredMod_natAbs_le (value modulus : Int)
    (modulusPositive : 0 < modulus) :
    (centeredMod value modulus).natAbs ≤ modulus.natAbs := by
  let residue := value % modulus
  have modulusNonzero := ne_of_gt modulusPositive
  have residueNonnegative : 0 ≤ residue := Int.emod_nonneg value modulusNonzero
  have residueLess : residue < modulus := by
    have := Int.emod_lt value modulusNonzero
    rw [Int.natAbs_of_nonneg (le_of_lt modulusPositive)] at this
    exact this
  rw [centeredMod]
  split
  · apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs, abs_of_nonpos (by omega),
      Int.natAbs_of_nonneg (le_of_lt modulusPositive)]
    omega
  · apply Int.ofNat_le.mp
    rw [Int.natAbs_of_nonneg residueNonnegative,
      Int.natAbs_of_nonneg (le_of_lt modulusPositive)]
    exact le_of_lt residueLess

theorem setEntry_entriesBounded {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (selectedRow : Fin m) (selectedColumn : Fin n) (value : Int)
    (bound : Nat) (bounded : EntriesBounded A bound)
    (valueBound : value.natAbs ≤ bound) :
    EntriesBounded (setEntry A selectedRow selectedColumn value) bound := by
  intro row column
  by_cases rowEq : row = selectedRow
  · subst row
    by_cases columnEq : column = selectedColumn
    · subst column
      simpa using valueBound
    · simpa [setEntry, columnEq] using bounded selectedRow column
  · simpa [setEntry, rowEq] using bounded row column

theorem replacePairSuffix_entriesBounded {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) (modulus : Int)
    (u v pivotDivGcd targetDivGcd : Int)
    (bound : Nat) (bounded : EntriesBounded A bound)
    (modulusPositive : 0 < modulus)
    (modulusBound : modulus.natAbs ≤ bound) :
    EntriesBounded
      (replacePairSuffix A pivot target column modulus
        u v pivotDivGcd targetDivGcd) bound := by
  intro row currentColumn
  rw [replacePairSuffix]
  split
  · exact bounded row currentColumn
  · split
    · exact (centeredMod_natAbs_le _ modulus modulusPositive).trans modulusBound
    · split
      · exact (centeredMod_natAbs_le _ modulus modulusPositive).trans modulusBound
      · exact bounded row currentColumn

theorem reduceBelowRow_entriesBounded {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) (modulus : Int)
    (bound : Nat) (bounded : EntriesBounded A bound)
    (modulusPositive : 0 < modulus)
    (modulusBound : modulus.natAbs ≤ bound) :
    EntriesBounded
      (reduceBelowRow A pivot target column modulus).1 bound := by
  rw [reduceBelowRow]
  split
  · exact bounded
  · exact replacePairSuffix_entriesBounded A pivot target column modulus
      _ _ _ _ bound bounded modulusPositive modulusBound

theorem reduceBelow_entriesBounded {m n : Nat}
    (pivot : Fin m) (column : Fin n) (modulus : Int)
    (targets : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (bound : Nat) (bounded : EntriesBounded A bound)
    (modulusPositive : 0 < modulus)
    (modulusBound : modulus.natAbs ≤ bound) :
    EntriesBounded
      (reduceBelow pivot column modulus targets A).1 bound := by
  induction targets generalizing A with
  | nil => simpa [reduceBelow] using bounded
  | cons target tail ih =>
      rw [reduceBelow]
      split
      · apply ih
        exact reduceBelowRow_entriesBounded A pivot target column modulus
          bound bounded modulusPositive modulusBound
      · exact ih A bounded

theorem scalePivotSuffix_entriesBounded {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (coefficient modulus : Int)
    (bound : Nat) (bounded : EntriesBounded A bound)
    (modulusPositive : 0 < modulus)
    (modulusBound : modulus.natAbs ≤ bound) :
    EntriesBounded
      (scalePivotSuffix A pivot column coefficient modulus) bound := by
  intro row currentColumn
  rw [scalePivotSuffix]
  split
  · exact (emod_natAbs_le _ modulus modulusPositive).trans modulusBound
  · exact bounded row currentColumn

theorem reduceAboveRow_entriesBounded {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n)
    (bound : Nat) (bounded : EntriesBounded A bound) :
    EntriesBounded (reduceAboveRow A pivot target column)
      (coefficientGrowth bound) := by
  intro row currentColumn
  by_cases update : row = target ∧ column ≤ currentColumn
  · obtain ⟨rowEq, after⟩ := update
    subst row
    let quotient := A target column / A pivot column
    have quotientBound : quotient.natAbs ≤ bound := by
      have absolute := Int.abs_ediv_le_abs (A target column) (A pivot column)
      have quotientLe : quotient.natAbs ≤ (A target column).natAbs := by
        apply Int.ofNat_le.mp
        rw [Int.natCast_natAbs, Int.natCast_natAbs]
        simpa [quotient] using absolute
      exact quotientLe.trans (bounded target column)
    simp only [reduceAboveRow, true_and, after, if_true]
    change (A target currentColumn -
      quotient * A pivot currentColumn).natAbs ≤ coefficientGrowth bound
    calc
      (A target currentColumn - quotient * A pivot currentColumn).natAbs ≤
          (A target currentColumn).natAbs +
            (quotient * A pivot currentColumn).natAbs :=
        Int.natAbs_sub_le _ _
      _ = (A target currentColumn).natAbs +
            quotient.natAbs * (A pivot currentColumn).natAbs := by
        rw [Int.natAbs_mul]
      _ ≤ bound + bound * bound :=
        Nat.add_le_add (bounded target currentColumn)
          (Nat.mul_le_mul quotientBound (bounded pivot currentColumn))
      _ = coefficientGrowth bound := rfl
  · simp only [reduceAboveRow, update, if_false]
    exact (bounded row currentColumn).trans (coefficientGrowth_le bound)

theorem reduceAbove_entriesBounded {m n : Nat}
    (pivot : Fin m) (column : Fin n)
    (targets : List (Fin m))
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (bound : Nat) (bounded : EntriesBounded A bound) :
    EntriesBounded (reduceAbove pivot column targets A)
      (coefficientSteps targets.length bound) := by
  induction targets generalizing A bound with
  | nil => simpa [reduceAbove, coefficientSteps] using bounded
  | cons target tail ih =>
      rw [reduceAbove]
      split
      · rw [List.length_cons, coefficientSteps]
        exact ih (reduceAboveRow A pivot target column)
          (coefficientGrowth bound)
          (reduceAboveRow_entriesBounded A pivot target column bound bounded)
      · have tailBound := ih A bound bounded
        rw [List.length_cons, coefficientSteps]
        exact EntriesBounded.mono tailBound
          (coefficientSteps_mono tail.length (coefficientGrowth_le bound))

theorem stage_entriesBounded {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column : Fin n) (bound : Nat)
    (bounded : EntriesBounded state.candidate bound)
    (modulusPositive : 0 < state.finalModulus)
    (modulusBound : state.finalModulus.natAbs ≤ bound) :
    EntriesBounded (stage columns_le_rows state column).candidate
      (coefficientSteps m bound) := by
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
  have preparedBounded : EntriesBounded prepared bound := by
    by_cases pivotZero : state.candidate pivot column = 0
    · rw [show prepared = setEntry state.candidate pivot column modulus by
        simp [prepared, pivotZero]]
      exact setEntry_entriesBounded state.candidate pivot column modulus
        bound bounded modulusBound
    · simpa [prepared, pivotZero] using bounded
  have belowBounded : EntriesBounded below.1 bound :=
    reduceBelow_entriesBounded pivot column modulus (List.finRange m)
      prepared bound preparedBounded (by simpa [modulus] using modulusPositive)
      (by simpa [modulus] using modulusBound)
  have scaledBounded : EntriesBounded scaled bound :=
    scalePivotSuffix_entriesBounded below.1 pivot column gcdData.leftCoeff
      modulus bound belowBounded (by simpa [modulus] using modulusPositive)
      (by simpa [modulus] using modulusBound)
  have restoredBounded : EntriesBounded restored bound := by
    by_cases scaledZero : scaled pivot column = 0
    · rw [show restored = setEntry scaled pivot column modulus by
        simp [restored, scaledZero]]
      exact setEntry_entriesBounded scaled pivot column modulus bound
        scaledBounded (by simpa [modulus] using modulusBound)
    · simpa [restored, scaledZero] using scaledBounded
  have reducedBounded : EntriesBounded reduced
      (coefficientSteps m bound) := by
    have result := reduceAbove_entriesBounded pivot column
      (List.finRange m).reverse restored bound restoredBounded
    simpa [reduced] using result
  simpa [stage, pivot, modulus, prepared, below, gcdData, scaled, restored,
    reduced] using reducedBounded

theorem stage_modulus_positive {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column : Fin n) (modulusPositive : 0 < state.finalModulus) :
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
  change 0 < modulus / gcdData.gcd
  simpa [gcdData, modulus] using
    (pivotModulusQuotient_positive
      (value := below.1 pivot column) modulusPositive)

theorem stage_modulus_natAbs_le {m n : Nat}
    (columns_le_rows : n ≤ m) (state : RawModularRun m n)
    (column : Fin n) (bound : Nat)
    (modulusBound : state.finalModulus.natAbs ≤ bound) :
    (stage columns_le_rows state column).finalModulus.natAbs ≤
      coefficientSteps m bound := by
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := reduceBelow pivot column modulus (List.finRange m) prepared
  let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
  have quotientLe : (modulus / gcdData.gcd).natAbs ≤ modulus.natAbs := by
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs, Int.natCast_natAbs]
    exact Int.abs_ediv_le_abs modulus gcdData.gcd
  change (modulus / gcdData.gcd).natAbs ≤ coefficientSteps m bound
  exact (quotientLe.trans (by simpa [modulus] using modulusBound)).trans
    (coefficientSteps_base_le m bound)

theorem runColumns_entriesBounded {m n : Nat}
    (columns_le_rows : n ≤ m) (columns : List (Fin n))
    (state : RawModularRun m n) (bound : Nat)
    (bounded : EntriesBounded state.candidate bound)
    (modulusPositive : 0 < state.finalModulus)
    (modulusBound : state.finalModulus.natAbs ≤ bound) :
    EntriesBounded
        (runColumns columns_le_rows columns state).candidate
        (coefficientSteps (columns.length * m) bound) ∧
      0 < (runColumns columns_le_rows columns state).finalModulus ∧
      (runColumns columns_le_rows columns state).finalModulus.natAbs ≤
        coefficientSteps (columns.length * m) bound := by
  induction columns generalizing state bound with
  | nil =>
      simpa [runColumns, coefficientSteps] using
        And.intro bounded (And.intro modulusPositive modulusBound)
  | cons column tail ih =>
      let next := stage columns_le_rows state column
      have nextBounded : EntriesBounded next.candidate
          (coefficientSteps m bound) :=
        stage_entriesBounded columns_le_rows state column bound bounded
          modulusPositive modulusBound
      have nextPositive : 0 < next.finalModulus :=
        stage_modulus_positive columns_le_rows state column modulusPositive
      have nextModulusBound : next.finalModulus.natAbs ≤
          coefficientSteps m bound :=
        stage_modulus_natAbs_le columns_le_rows state column bound modulusBound
      have tailResult := ih next (coefficientSteps m bound) nextBounded
        nextPositive nextModulusBound
      rw [runColumns]
      have stepsEq :
          coefficientSteps (tail.length * m)
              (coefficientSteps m bound) =
            coefficientSteps ((tail.length + 1) * m) bound := by
        rw [← coefficientSteps_add]
        congr 1
        ring
      simpa only [List.length_cons, stepsEq] using tailResult

end Internal

/-- Execute exactly the first `processed` canonical columns of the raw kernel. -/
@[expose] public def runRawPrefix {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) (processed : Nat) :
    RawModularRun m n :=
  Internal.runColumns columns_le_rows
    ((List.finRange n).take processed)
    { candidate := A
      finalModulus := modulus
      stages := []
      operations := {} }

/-- Coefficient envelope after an arbitrary canonical-column prefix. -/
@[expose] public def modularIntermediateHeightBound
    (rows columns processed inputHeight modulusHeight : Nat) : Nat :=
  coefficientSteps (min processed columns * rows)
    (max inputHeight modulusHeight)

public theorem runRawPrefix_entriesBounded {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) (processed : Nat)
    (modulusPositive : 0 < modulus) :
    EntriesBounded (runRawPrefix A columns_le_rows modulus processed).candidate
      (modularIntermediateHeightBound m n processed
        (matrixHeight A) modulus.natAbs) := by
  let initialBound := max (matrixHeight A) modulus.natAbs
  have inputBounded : EntriesBounded A initialBound := by
    intro row column
    exact (entry_natAbs_le_matrixHeight A row column).trans
      (Nat.le_max_left _ _)
  have modulusBound : modulus.natAbs ≤ initialBound := Nat.le_max_right _ _
  have result := Internal.runColumns_entriesBounded columns_le_rows
    ((List.finRange n).take processed)
    ({ candidate := A
       finalModulus := modulus
       stages := []
       operations := {} } : RawModularRun m n)
    initialBound inputBounded modulusPositive modulusBound
  simpa [runRawPrefix, modularIntermediateHeightBound, initialBound,
    List.length_take] using result.1

public theorem runRawPrefix_matrixHeight_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) (processed : Nat)
    (modulusPositive : 0 < modulus) :
    matrixHeight (runRawPrefix A columns_le_rows modulus processed).candidate ≤
      modularIntermediateHeightBound m n processed
        (matrixHeight A) modulus.natAbs := by
  exact matrixHeight_le fun row column =>
    runRawPrefix_entriesBounded A columns_le_rows modulus processed
      modulusPositive row column

public theorem runRawPrefix_matrixBitLength_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) (processed : Nat)
    (modulusPositive : 0 < modulus) :
    matrixBitLength (runRawPrefix A columns_le_rows modulus processed).candidate ≤
      Nat.size (modularIntermediateHeightBound m n processed
        (matrixHeight A) modulus.natAbs) := by
  exact Nat.size_le_size
    (runRawPrefix_matrixHeight_le A columns_le_rows modulus processed
      modulusPositive)

public theorem runRaw_eq_runRawPrefix {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) :
    runRaw A columns_le_rows modulus =
      runRawPrefix A columns_le_rows modulus n := by
  unfold runRaw runRawPrefix
  rw [List.take_of_length_le (by simp)]

public theorem runRaw_matrixHeight_le_intermediateBound {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int)
    (modulusPositive : 0 < modulus) :
    matrixHeight (runRaw A columns_le_rows modulus).candidate ≤
      modularIntermediateHeightBound m n n
        (matrixHeight A) modulus.natAbs := by
  rw [runRaw_eq_runRawPrefix]
  exact runRawPrefix_matrixHeight_le A columns_le_rows modulus n
    modulusPositive

public theorem runRaw_matrixBitLength_le_intermediateBound {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int)
    (modulusPositive : 0 < modulus) :
    matrixBitLength (runRaw A columns_le_rows modulus).candidate ≤
      Nat.size (modularIntermediateHeightBound m n n
        (matrixHeight A) modulus.natAbs) := by
  exact Nat.size_le_size
    (runRaw_matrixHeight_le_intermediateBound A columns_le_rows modulus
      modulusPositive)

public theorem diagonal_natAbs_le_modulus {m n : Nat}
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m)
    (shape : ProcessedHermiteShape columns_le_rows H n)
    (modulus : Int) (modulusPositive : 0 < modulus)
    (detDvd : (suffixSquare H columns_le_rows 0).det ∣ modulus)
    (column : Fin n) :
    (H (Fin.castLE columns_le_rows column) column).natAbs ≤
      modulus.natAbs := by
  let selected : SuffixIndex n 0 := ⟨column, Nat.zero_le column.val⟩
  let diagonal : SuffixIndex n 0 → Int := fun current =>
    H (Fin.castLE columns_le_rows current.1) current.1
  have factorDvdProduct : diagonal selected ∣ ∏ current, diagonal current := by
    exact Finset.dvd_prod_of_mem diagonal (Finset.mem_univ selected)
  have factorDvdDet :
      H (Fin.castLE columns_le_rows column) column ∣
        (suffixSquare H columns_le_rows 0).det := by
    rw [suffixSquare_det_eq_prod H columns_le_rows shape]
    simpa [selected, diagonal] using factorDvdProduct
  have factorDvdModulus :
      H (Fin.castLE columns_le_rows column) column ∣ modulus :=
    dvd_trans factorDvdDet detDvd
  exact Nat.le_of_dvd
    (Int.natAbs_pos.mpr (ne_of_gt modulusPositive))
    (Int.natAbs_dvd_natAbs.mpr factorDvdModulus)

public theorem entry_natAbs_le_modulus {m n : Nat}
    (H : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m)
    (shape : ProcessedHermiteShape columns_le_rows H n)
    (modulus : Int) (modulusPositive : 0 < modulus)
    (detDvd : (suffixSquare H columns_le_rows 0).det ∣ modulus)
    (row : Fin m) (column : Fin n) :
    (H row column).natAbs ≤ modulus.natAbs := by
  have pivotBound := diagonal_natAbs_le_modulus H columns_le_rows shape
    modulus modulusPositive detDvd column
  have columnShape := shape column column.isLt
  by_cases above : row.val < column.val
  · have rowBeforePivot : row < Fin.castLE columns_le_rows column := by
      exact above
    have reduced := columnShape.above_reduced row rowBeforePivot
    rw [reduced]
    have pivotNonzero :
        H (Fin.castLE columns_le_rows column) column ≠ 0 :=
      ne_of_gt columnShape.pivot_positive
    have remainderNonnegative := Int.emod_nonneg (H row column) pivotNonzero
    have remainderLess := Int.emod_lt (H row column) pivotNonzero
    have remainderAbsLe :
        (H row column % H (Fin.castLE columns_le_rows column) column).natAbs ≤
          (H (Fin.castLE columns_le_rows column) column).natAbs := by
      apply Int.ofNat_le.mp
      rw [Int.natAbs_of_nonneg remainderNonnegative]
      exact le_of_lt remainderLess
    exact remainderAbsLe.trans pivotBound
  · by_cases equal : row.val = column.val
    · have rowEq : row = Fin.castLE columns_le_rows column := by
        apply Fin.ext
        exact equal
      subst row
      exact pivotBound
    · have pivotBeforeRow : Fin.castLE columns_le_rows column < row := by
        change column.val < row.val
        omega
      rw [columnShape.below_zero row pivotBeforeRow]
      exact Nat.zero_le _

public theorem runWithDeterminantWitness_entry_natAbs_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank)
    (row : Fin m) (column : Fin n) :
    ((runWithDeterminantWitness A fullRank witness).candidate row column).natAbs ≤
      witness.modulus.natAbs := by
  let reference := hermiteNormalFormFin A
  have candidateEq :=
    runWithDeterminantWitness_candidate_eq_reference A fullRank witness
  rw [candidateEq]
  have referenceShape := hnf_fullColumnShape reference.H
    fullRank.columns_le_rows reference.isHermite
    (cols_linearIndependent_of_rank_eq_width _
      (reference_rank_eq_width A fullRank))
  exact entry_natAbs_le_modulus reference.H fullRank.columns_le_rows
    (fun current _ => referenceShape.2 current) witness.modulus witness.positive
    (reference_initialDet_dvd_modulus A fullRank witness) row column

public theorem runWithDeterminantWitness_matrixHeight_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) :
    matrixHeight (runWithDeterminantWitness A fullRank witness).candidate ≤
      witness.modulus.natAbs := by
  exact matrixHeight_le fun row column =>
    runWithDeterminantWitness_entry_natAbs_le A fullRank witness row column

public theorem runWithDeterminantWitness_matrixBitLength_le {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) :
    matrixBitLength (runWithDeterminantWitness A fullRank witness).candidate ≤
      integerBitLength witness.modulus := by
  exact Nat.size_le_size
    (runWithDeterminantWitness_matrixHeight_le A fullRank witness)

end NormalForms.Research.ModularHNF
