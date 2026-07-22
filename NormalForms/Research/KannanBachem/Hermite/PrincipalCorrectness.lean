/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.Principal
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal
import all NormalForms.Matrix.Hermite.Defs
import Mathlib.LinearAlgebra.Matrix.Block

/-! Correctness invariants for the principal-minor HNF schedule. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix BigOperators
open NormalForms
open NormalForms.Matrix.Hermite

namespace Principal

/-- The first nonzero search returns a specified pivot after a zero prefix. -/
theorem firstNonzero?_eq_some_of_before_eq_zero {R : Type _}
    [Zero R] [DecidableEq R] :
    {n : Nat} → (row : Fin n → R) → (pivot : Fin n) →
      (∀ column, column < pivot → row column = 0) → row pivot ≠ 0 →
        firstNonzero? row = some pivot
  | 0, _, pivot, _, _ => Fin.elim0 pivot
  | n + 1, row, pivot, hbefore, hpivot => by
      cases pivot using Fin.cases with
      | zero =>
          simp [firstNonzero?, hpivot]
      | succ pivot =>
          have hzero : row 0 = 0 := hbefore 0 (by
            change 0 < pivot.val + 1
            omega)
          rw [firstNonzero?, hzero]
          have tail := firstNonzero?_eq_some_of_before_eq_zero
            (fun column : Fin n => row column.succ) pivot
            (by
              intro column hcolumn
              exact hbefore column.succ
                (Fin.succ_lt_succ_iff.mpr hcolumn))
            hpivot
          simp [tail]

/-- HNF conditions restricted to a leading square block. -/
structure PrefixHermite {n : Nat} (bound : Nat)
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Prop where
  diagonal : ∀ row, row.val < bound →
    A row row = _root_.normalize (A row row)
  below : ∀ row column, row.val < bound → column < row →
    A row column = 0
  reduced : ∀ row column, column.val < bound → row < column →
    A row column = A row column % A column column

theorem PrefixHermite.mono {n bound smaller : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (h : PrefixHermite bound A) (hle : smaller ≤ bound) :
    PrefixHermite smaller A :=
  { diagonal := fun row hrow => h.diagonal row (by omega)
    below := fun row column hrow hlt => h.below row column (by omega) hlt
    reduced := fun row column hcolumn hlt =>
      h.reduced row column (by omega) hlt }

theorem PrefixHermite.zero {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : PrefixHermite 0 A :=
  { diagonal := by omega
    below := by omega
    reduced := by omega }

theorem PrefixHermite.lowerRight {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (h : PrefixHermite (n + 1) A) :
    PrefixHermite n (lowerRight A) :=
  { diagonal := by
      intro row hrow
      exact h.diagonal row.succ (by omega)
    below := by
      intro row column hrow hlt
      exact h.below row.succ column.succ (by omega)
        (Fin.succ_lt_succ_iff.mpr hlt)
    reduced := by
      intro row column hcolumn hlt
      exact h.reduced row.succ column.succ (by omega)
        (Fin.succ_lt_succ_iff.mpr hlt) }

theorem PrefixHermite.toHermite {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int)
    (hprefix : PrefixHermite n A)
    (diagonal_ne : ∀ row, A row row ≠ 0) :
    IsHermiteNormalFormFin A := by
  induction n with
  | zero => exact .emptyRows A
  | succ n ih =>
      refine .pivot A (diagonal_ne 0) (hprefix.diagonal 0 (by omega)) ?_ ?_ ?_
      · intro row
        exact hprefix.below row.succ 0 (by omega) (by
          change 0 < row.val + 1
          omega)
      · apply ih
        · exact hprefix.lowerRight
        · intro row
          exact diagonal_ne row.succ
      · intro row
        have first :
            firstNonzero? (fun column : Fin n => A row.succ column.succ) =
              some row := by
          apply firstNonzero?_eq_some_of_before_eq_zero
          · intro column hcolumn
            exact hprefix.below row.succ column.succ (by omega)
              (Fin.succ_lt_succ_iff.mpr hcolumn)
          · exact diagonal_ne row.succ
        rw [first]
        exact hprefix.reduced 0 row.succ (by omega) (by
          change 0 < row.val + 1
          omega)

theorem State.reduceAbove_apply_before {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    (state : State A)
    (pivotZero : ∀ column, column < destination →
      state.transform.B destination column = 0)
    (row column : Fin n) (hcolumn : column < destination) :
    (state.reduceAbove source destination hlt).transform.B row column =
      state.transform.B row column := by
  by_cases hrow : row = source
  · subst row
    rw [State.reduceAbove_source_apply, pivotZero column hcolumn]
    ring
  · exact State.reduceAbove_other_apply source destination row hlt hrow state column

theorem PrefixHermite.reduceAbove {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    (state : State A)
    (leading : PrefixHermite destination.val state.transform.B)
    (pivotZero : ∀ column, column < destination →
      state.transform.B destination column = 0) :
    PrefixHermite destination.val
      (state.reduceAbove source destination hlt).transform.B :=
  { diagonal := by
      intro row hrow
      have hltRow : row < destination := hrow
      rw [State.reduceAbove_apply_before source destination hlt state
        pivotZero row row hltRow]
      exact leading.diagonal row hrow
    below := by
      intro row column hrow hcolumn
      have hltColumn : column < destination := lt_trans hcolumn hrow
      rw [State.reduceAbove_apply_before source destination hlt state
        pivotZero row column hltColumn]
      exact leading.below row column hrow hcolumn
    reduced := by
      intro row column hcolumn hltRow
      have hltColumn : column < destination := hcolumn
      rw [State.reduceAbove_apply_before source destination hlt state
          pivotZero row column hltColumn,
        State.reduceAbove_apply_before source destination hlt state
          pivotZero column column hltColumn]
      exact leading.reduced row column hcolumn hltRow }

theorem reduceAboveLoop_row_unchanged {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      (row column : Fin n) → k ≤ row.val →
        (reduceAboveLoop destination k hk state).transform.B row column =
          state.transform.B row column
  | 0, _, _, _, _, _ => rfl
  | k + 1, hk, state, row, column, hrow => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have hsource : source < destination := by
        change k < destination.val
        omega
      have hne : row ≠ source := by
        intro equality
        have values := congrArg Fin.val equality
        dsimp [source] at values
        omega
      change
        (previous.reduceAbove source destination hsource).transform.B row column =
          state.transform.B row column
      rw [State.reduceAbove_other_apply source destination row hsource hne]
      exact reduceAboveLoop_row_unchanged destination k (by omega) state
        row column (by omega)

/-- Invariant while reducing one newly constructed pivot column. -/
structure ReductionInvariant {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) (processed : Nat) (state : State A) : Prop where
  processed_le : processed ≤ destination.val
  leading : PrefixHermite destination.val state.transform.B
  pivotZero : ∀ column, column < destination →
    state.transform.B destination column = 0
  pivotNormalized :
    state.transform.B destination destination =
      _root_.normalize (state.transform.B destination destination)
  reducedNew : ∀ row, row.val < processed →
    state.transform.B row destination =
      state.transform.B row destination %
        state.transform.B destination destination

theorem ReductionInvariant.step {n k : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {destination : Fin n} {state : State A}
    (invariant : ReductionInvariant destination k state)
    (hk : k < destination.val) :
    let source : Fin n := ⟨k, by omega⟩
    ReductionInvariant destination (k + 1)
      (state.reduceAbove source destination (by omega)) := by
  let source : Fin n := ⟨k, by omega⟩
  have hsource : source < destination := by
    change k < destination.val
    exact hk
  let next := state.reduceAbove source destination hsource
  have destination_ne : destination ≠ source := hsource.ne'
  exact
    { processed_le := by omega
      leading := invariant.leading.reduceAbove source destination hsource state
        invariant.pivotZero
      pivotZero := by
        intro column hcolumn
        rw [State.reduceAbove_other_apply source destination destination hsource
          destination_ne]
        exact invariant.pivotZero column hcolumn
      pivotNormalized := by
        rw [State.reduceAbove_other_apply source destination destination hsource
          destination_ne]
        exact invariant.pivotNormalized
      reducedNew := by
        intro row hrow
        by_cases hold : row.val < k
        · have row_ne : row ≠ source := by
            intro equality
            have values := congrArg Fin.val equality
            dsimp [source] at values
            omega
          rw [State.reduceAbove_other_apply source destination row hsource row_ne,
            State.reduceAbove_other_apply source destination destination hsource
              destination_ne]
          exact invariant.reducedNew row hold
        · have values : row.val = k := by omega
          have equality : row = source := Fin.ext values
          subst row
          exact State.reduceAbove_reduced source destination hsource state }

theorem reduceAboveLoop_invariant {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      ReductionInvariant destination 0 state →
        ReductionInvariant destination k
          (reduceAboveLoop destination k hk state)
  | 0, _, _, invariant => invariant
  | k + 1, hk, state, invariant => by
      let previous := reduceAboveLoop destination k (by omega) state
      have previousInvariant := reduceAboveLoop_invariant destination k
        (by omega) state invariant
      exact previousInvariant.step (by omega)

theorem ReductionInvariant.finish {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {destination : Fin n} {state : State A}
    (invariant : ReductionInvariant destination destination.val state) :
    PrefixHermite (destination.val + 1) state.transform.B :=
  { diagonal := by
      intro row hrow
      by_cases hold : row.val < destination.val
      · exact invariant.leading.diagonal row hold
      · have values : row.val = destination.val := by omega
        have equality : row = destination := Fin.ext values
        subst row
        exact invariant.pivotNormalized
    below := by
      intro row column hrow hcolumn
      by_cases hold : row.val < destination.val
      · exact invariant.leading.below row column hold hcolumn
      · have values : row.val = destination.val := by omega
        have equality : row = destination := Fin.ext values
        subst row
        exact invariant.pivotZero column hcolumn
    reduced := by
      intro row column hcolumn hrow
      by_cases hold : column.val < destination.val
      · exact invariant.leading.reduced row column hold hrow
      · have values : column.val = destination.val := by omega
        have equality : column = destination := Fin.ext values
        subst column
        exact invariant.reducedNew row hrow }

theorem State.gcdEliminate_apply_before_row {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : State A) (row column : Fin n) (hrow : row < pivot) :
    (state.gcdEliminate pivot target hlt).transform.B row column =
      state.transform.B row column := by
  apply State.gcdEliminate_other_apply pivot target row hlt
  · exact hrow.ne
  · exact (lt_trans hrow hlt).ne

theorem PrefixHermite.gcdEliminate_before {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (state : State A)
    (leading : PrefixHermite pivot.val state.transform.B) :
    PrefixHermite pivot.val
      (state.gcdEliminate pivot target hlt).transform.B :=
  { diagonal := by
      intro row hrow
      have hltRow : row < pivot := hrow
      rw [State.gcdEliminate_apply_before_row pivot target hlt state row row hltRow]
      exact leading.diagonal row hrow
    below := by
      intro row column hrow hcolumn
      have hltRow : row < pivot := hrow
      rw [State.gcdEliminate_apply_before_row pivot target hlt state row column hltRow]
      exact leading.below row column hrow hcolumn
    reduced := by
      intro row column hcolumn hrow
      have hltColumn : column < pivot := hcolumn
      have hltRow : row < pivot := lt_trans hrow hltColumn
      rw [State.gcdEliminate_apply_before_row pivot target hlt state row column hltRow,
        State.gcdEliminate_apply_before_row pivot target hlt state column column
          hltColumn]
      exact leading.reduced row column hcolumn hrow }

/-- Invariant while clearing the new row against earlier pivots. -/
structure EliminationInvariant {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (processed : Nat) (state : State A) : Prop where
  processed_le : processed ≤ target.val
  leading : PrefixHermite processed state.transform.B
  targetZero : ∀ column, column.val < processed →
    state.transform.B target column = 0
  futureBelow : ∀ row, processed ≤ row.val → row < target →
    ∀ column, column < row → state.transform.B row column = 0

theorem EliminationInvariant.initial {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A)
    (leading : PrefixHermite target.val state.transform.B) :
    EliminationInvariant target 0 state :=
  { processed_le := by omega
    leading := PrefixHermite.zero _
    targetZero := by omega
    futureBelow := by
      intro row _ hrow column hcolumn
      exact leading.below row column hrow hcolumn }

theorem EliminationInvariant.step {n k : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {target : Fin n} {state : State A}
    (invariant : EliminationInvariant target k state)
    (hk : k < target.val) :
    let pivot : Fin n := ⟨k, by omega⟩
    let eliminated := state.gcdEliminate pivot target (by omega)
    let reduced := reduceAboveLoop pivot pivot.val le_rfl eliminated
    EliminationInvariant target (k + 1) reduced := by
  let pivot : Fin n := ⟨k, by omega⟩
  have hpivot : pivot < target := by
    change k < target.val
    exact hk
  let eliminated := state.gcdEliminate pivot target hpivot
  have pivotBefore : ∀ column, column < pivot →
      state.transform.B pivot column = 0 := by
    intro column hcolumn
    exact invariant.futureBelow pivot (by
      change k ≤ k
      omega) hpivot column hcolumn
  have targetBefore : ∀ column, column < pivot →
      state.transform.B target column = 0 := by
    intro column hcolumn
    exact invariant.targetZero column hcolumn
  have eliminatedPivotZero : ∀ column, column < pivot →
      eliminated.transform.B pivot column = 0 := by
    intro column hcolumn
    rw [State.gcdEliminate_pivot_apply]
    simp [pivotBefore column hcolumn, targetBefore column hcolumn]
  have reductionInitial : ReductionInvariant pivot 0 eliminated :=
    { processed_le := by omega
      leading := invariant.leading.gcdEliminate_before pivot target hpivot state
      pivotZero := eliminatedPivotZero
      pivotNormalized := State.gcdEliminate_pivot_normalized pivot target hpivot state
      reducedNew := by omega }
  let reduced := reduceAboveLoop pivot pivot.val le_rfl eliminated
  have reductionFinal : ReductionInvariant pivot pivot.val reduced :=
    reduceAboveLoop_invariant pivot pivot.val le_rfl eliminated reductionInitial
  have targetAfterEliminate : ∀ column, column.val < k + 1 →
      eliminated.transform.B target column = 0 := by
    intro column hcolumn
    by_cases hold : column.val < k
    · have hltColumn : column < pivot := hold
      rw [State.gcdEliminate_target_apply]
      simp [pivotBefore column hltColumn, targetBefore column hltColumn]
    · have values : column.val = k := by omega
      have equality : column = pivot := Fin.ext values
      subst column
      exact State.gcdEliminate_target_pivot pivot target hpivot state
  exact
    { processed_le := by omega
      leading := reductionFinal.finish
      targetZero := by
        intro column hcolumn
        rw [reduceAboveLoop_row_unchanged pivot pivot.val le_rfl eliminated
          target column (by
            change k ≤ target.val
            omega)]
        exact targetAfterEliminate column hcolumn
      futureBelow := by
        intro row hprocessed hrow column hcolumn
        rw [reduceAboveLoop_row_unchanged pivot pivot.val le_rfl eliminated
          row column (by
            change k ≤ row.val
            omega)]
        have row_ne_pivot : row ≠ pivot := by
          intro equality
          have values := congrArg Fin.val equality
          dsimp [pivot] at values
          omega
        have row_ne_target : row ≠ target := hrow.ne
        rw [State.gcdEliminate_other_apply pivot target row hpivot
          row_ne_pivot row_ne_target]
        exact invariant.futureBelow row (by omega) hrow column hcolumn }

theorem eliminateStageLoop_invariant {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      PrefixHermite target.val state.transform.B →
        EliminationInvariant target k
          (eliminateStageLoop target k hk state)
  | 0, _, state, leading =>
      EliminationInvariant.initial target state leading
  | k + 1, hk, state, leading => by
      let previous := eliminateStageLoop target k (by omega) state
      have previousInvariant := eliminateStageLoop_invariant target k
        (by omega) state leading
      exact previousInvariant.step (by omega)

theorem PrefixHermite.normalize_after {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A)
    (leading : PrefixHermite target.val state.transform.B) :
    PrefixHermite target.val (state.normalize target).transform.B :=
  { diagonal := by
      intro row hrow
      have hne : row ≠ target := by
        intro equality
        have values := congrArg Fin.val equality
        omega
      rw [State.normalize_other_apply target row hne]
      exact leading.diagonal row hrow
    below := by
      intro row column hrow hcolumn
      have hne : row ≠ target := by
        intro equality
        have values := congrArg Fin.val equality
        omega
      rw [State.normalize_other_apply target row hne]
      exact leading.below row column hrow hcolumn
    reduced := by
      intro row column hcolumn hrow
      have row_ne : row ≠ target := by
        intro equality
        have values := congrArg Fin.val equality
        omega
      have column_ne : column ≠ target := by
        intro equality
        have values := congrArg Fin.val equality
        omega
      rw [State.normalize_other_apply target row row_ne,
        State.normalize_other_apply target column column_ne]
      exact leading.reduced row column hcolumn hrow }

theorem extendStage_correct {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (state : State A)
    (leading : PrefixHermite target.val state.transform.B) :
    PrefixHermite (target.val + 1) (extendStage target state).transform.B := by
  let eliminated := eliminateStageLoop target target.val le_rfl state
  have eliminatedInvariant : EliminationInvariant target target.val eliminated :=
    eliminateStageLoop_invariant target target.val le_rfl state leading
  let normalized := eliminated.normalize target
  have normalizedZero : ∀ column, column < target →
      normalized.transform.B target column = 0 := by
    intro column hcolumn
    rw [State.normalize_row_apply, eliminatedInvariant.targetZero column hcolumn]
    ring
  have reductionInitial : ReductionInvariant target 0 normalized :=
    { processed_le := by omega
      leading := eliminatedInvariant.leading.normalize_after target eliminated
      pivotZero := normalizedZero
      pivotNormalized := State.normalize_diagonal target eliminated
      reducedNew := by omega }
  have reductionFinal := reduceAboveLoop_invariant target target.val le_rfl
    normalized reductionInitial
  exact reductionFinal.finish

theorem stageLoop_correct {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : State A) →
      PrefixHermite k (stageLoop k hk state).transform.B
  | 0, _, state => PrefixHermite.zero state.transform.B
  | k + 1, hk, state => by
      let previous := stageLoop k (by omega) state
      have previousCorrect := stageLoop_correct k (by omega) state
      exact extendStage_correct ⟨k, by omega⟩ previous previousCorrect

theorem compute_prefix {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    PrefixHermite n (compute A).transform.B :=
  stageLoop_correct n le_rfl (State.refl A)

theorem compute_det_ne_zero {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (compute A).transform.B.det ≠ 0 := by
  rw [← (compute A).transform.equation, _root_.Matrix.det_mul]
  exact mul_ne_zero
    (_root_.Matrix.det_ne_zero_of_left_inverse
      (compute A).transform.U_cert.left_inv)
    hdet

theorem compute_diagonal_ne {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    ∀ row, (compute A).transform.B row row ≠ 0 := by
  have upper : (compute A).transform.B.BlockTriangular id := by
    intro row column hcolumn
    exact (compute_prefix A).below row column row.isLt hcolumn
  have product_ne :
      (∏ row : Fin n, (compute A).transform.B row row) ≠ 0 := by
    rw [← _root_.Matrix.det_of_upperTriangular upper]
    exact compute_det_ne_zero A hdet
  exact fun row =>
    (Finset.prod_ne_zero_iff.mp product_ne) row (Finset.mem_univ row)

end Principal

/-- Every nonsingular square input makes the principal schedule produce HNF. -/
public theorem principalRun_isHermite_of_det_ne_zero {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    IsHermiteNormalFormFin (principalRun A).matrix := by
  change IsHermiteNormalFormFin (Principal.compute A).transform.B
  exact (Principal.compute_prefix A).toHermite _
    (Principal.compute_diagonal_ne A hdet)

/-- Total strong HNF result supplied directly by the principal schedule. -/
@[expose] public def principalHermiteNormalForm {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    HNFResultFin A :=
  { U := (principalRun A).steps.accumulator
    U_cert := (principalRun A).steps.accumulatorCertificate
    H := (principalRun A).matrix
    equation := (principalRun A).equation
    isHermite := principalRun_isHermite_of_det_ne_zero A hdet }

@[simp] public theorem principalHermiteNormalForm_H {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (principalHermiteNormalForm A hdet).H = (principalRun A).matrix := rfl

end NormalForms.Research.KannanBachem.Hermite
