/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalStageSize
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal
import all NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
import all NormalForms.Research.KannanBachem.Hermite.PrincipalPrefix
import Mathlib.Data.Fin.Tuple.Embedding

/-! Selected-minor invariants used in the stagewise coefficient proof. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix BigOperators
open Set
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

namespace Principal

theorem sum_embedding_eq_of_outside_zero {n r : Nat}
    (rows : Fin r ↪ Fin n) (f : Fin n → Int)
    (outside : ∀ index, index ∉ Set.range rows → f index = 0) :
    (∑ index : Fin r, f (rows index)) = ∑ index : Fin n, f index := by
  classical
  calc
    (∑ index : Fin r, f (rows index)) =
        Finset.sum (Finset.univ.map rows) f := by
      rw [Finset.sum_map]
    _ = Finset.sum Finset.univ f := by
      apply Finset.sum_subset
      · exact Finset.subset_univ _
      · intro index _ hnot
        apply outside index
        intro member
        rcases member with ⟨source, rfl⟩
        exact hnot (by simp)

/-- A matrix changes coordinates only among the rows selected by an embedding. -/
def ActsWithinRows {n r : Nat} (rows : Fin r ↪ Fin n)
    (U : _root_.Matrix (Fin n) (Fin n) Int) : Prop :=
  (∀ row, row ∈ Set.range rows → ∀ column, column ∉ Set.range rows →
    U row column = 0) ∧
  (∀ row, row ∉ Set.range rows → ∀ column,
    U row column = if row = column then 1 else 0)

theorem ActsWithinRows.one {n r : Nat} (rows : Fin r ↪ Fin n) :
    ActsWithinRows rows (1 : _root_.Matrix (Fin n) (Fin n) Int) := by
  constructor
  · intro row hrow column hcolumn
    have hne : row ≠ column := by
      intro equality
      subst column
      exact hcolumn hrow
    simp [hne]
  · intro row _ column
    rfl

theorem ActsWithinRows.mul {n r : Nat} {rows : Fin r ↪ Fin n}
    {U V : _root_.Matrix (Fin n) (Fin n) Int}
    (hU : ActsWithinRows rows U) (hV : ActsWithinRows rows V) :
    ActsWithinRows rows (U * V) := by
  classical
  constructor
  · intro row hrow column hcolumn
    rw [_root_.Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro middle _
    by_cases hmiddle : middle ∈ Set.range rows
    · rw [hV.1 middle hmiddle column hcolumn, mul_zero]
    · rw [hU.1 row hrow middle hmiddle, zero_mul]
  · intro row hrow column
    rw [_root_.Matrix.mul_apply]
    calc
      (∑ middle, U row middle * V middle column) =
          ∑ middle, (if row = middle then 1 else 0) * V middle column := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [hU.2 row hrow middle]
      _ = V row column := by simp
      _ = if row = column then 1 else 0 := hV.2 row hrow column

theorem ActsWithinRows.inverse {n r : Nat} {rows : Fin r ↪ Fin n}
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (support : ActsWithinRows rows U)
    (certificate : MatrixInverseCertificate U) :
    ActsWithinRows rows certificate.inverse := by
  classical
  constructor
  · intro row hrow column hcolumn
    have row_ne_column : row ≠ column := by
      intro equality
      subst column
      exact hcolumn hrow
    have columnIdentity : ∀ middle,
        U middle column = if middle = column then 1 else 0 := by
      intro middle
      by_cases hmiddle : middle ∈ Set.range rows
      · have middle_ne_column : middle ≠ column := by
          intro equality
          subst column
          exact hcolumn hmiddle
        rw [support.1 middle hmiddle column hcolumn, if_neg middle_ne_column]
      · exact support.2 middle hmiddle column
    have entry := congrFun (congrFun certificate.left_inv row) column
    rw [_root_.Matrix.mul_apply] at entry
    simp_rw [columnIdentity] at entry
    simpa [row_ne_column] using entry
  · intro row hrow column
    have entry := congrFun (congrFun certificate.right_inv row) column
    rw [_root_.Matrix.mul_apply] at entry
    simp_rw [support.2 row hrow] at entry
    change certificate.inverse row column =
      (1 : _root_.Matrix (Fin n) (Fin n) Int) row column
    simpa using entry

theorem ActsWithinRows.submatrix_mul {n r c : Nat}
    {rows : Fin r ↪ Fin n} (columns : Fin c → Fin n)
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (support : ActsWithinRows rows U)
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    U.submatrix rows rows * A.submatrix rows columns =
      (U * A).submatrix rows columns := by
  ext row column
  simp only [_root_.Matrix.submatrix_apply, _root_.Matrix.mul_apply]
  exact sum_embedding_eq_of_outside_zero rows
    (fun middle => U (rows row) middle * A middle (columns column))
    (by
      intro middle hmiddle
      rw [support.1 (rows row) ⟨row, rfl⟩ middle hmiddle, zero_mul])

def selectedSubmatrixCertificate {n r : Nat} (rows : Fin r ↪ Fin n)
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (support : ActsWithinRows rows U)
    (certificate : MatrixInverseCertificate U) :
    MatrixInverseCertificate (U.submatrix rows rows) :=
  { inverse := certificate.inverse.submatrix rows rows
    left_inv := by
      rw [support.inverse certificate |>.submatrix_mul rows U,
        certificate.left_inv]
      ext row column
      simp only [_root_.Matrix.submatrix_apply, _root_.Matrix.one_apply]
      simp [rows.injective.eq_iff]
    right_inv := by
      rw [support.submatrix_mul rows certificate.inverse, certificate.right_inv]
      ext row column
      simp only [_root_.Matrix.submatrix_apply, _root_.Matrix.one_apply]
      simp [rows.injective.eq_iff] }

theorem Transform.selectedSubmatrix_equation {n r c : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (rows : Fin r ↪ Fin n) (columns : Fin c → Fin n)
    (transform : Transform A)
    (support : ActsWithinRows rows transform.U) :
    transform.U.submatrix rows rows * A.submatrix rows columns =
      transform.B.submatrix rows columns := by
  calc
    transform.U.submatrix rows rows * A.submatrix rows columns =
        (transform.U * A).submatrix rows columns :=
      support.submatrix_mul columns A
    _ = transform.B.submatrix rows columns := by rw [transform.equation]

theorem twoRowLiftMatrix_actsWithinRows {n r : Nat}
    {rows : Fin r ↪ Fin n} (pivot target : Fin n)
    (pair : _root_.Matrix (Fin 2) (Fin 2) Int)
    (hpivot : pivot ∈ Set.range rows) (htarget : target ∈ Set.range rows)
    (hne : pivot ≠ target) :
    ActsWithinRows rows (twoRowLiftMatrix pivot target pair) := by
  classical
  constructor
  · intro row hrow column hcolumn
    by_cases hp : row = pivot
    · subst row
      have hpj : pivot ≠ column := fun equality =>
        hcolumn (equality ▸ hpivot)
      have htj : target ≠ column := fun equality =>
        hcolumn (equality ▸ htarget)
      simp [twoRowLiftMatrix_apply_pivot, hne, hpj, htj]
    · by_cases ht : row = target
      · subst row
        have hpj : pivot ≠ column := fun equality =>
          hcolumn (equality ▸ hpivot)
        have htj : target ≠ column := fun equality =>
          hcolumn (equality ▸ htarget)
        simp [twoRowLiftMatrix_apply_target, hpj, htj]
      · rw [twoRowLiftMatrix_apply_other pivot target row hp ht]
        have hne' : row ≠ column := fun equality =>
          hcolumn (equality ▸ hrow)
        simp [hne']
  · intro row hrow column
    have hp : row ≠ pivot := fun equality =>
      hrow (equality ▸ hpivot)
    have ht : row ≠ target := fun equality =>
      hrow (equality ▸ htarget)
    rw [twoRowLiftMatrix_apply_other pivot target row hp ht]
    rfl

theorem rowAddMatrix_actsWithinRows {n r : Nat}
    {rows : Fin r ↪ Fin n} (source destination : Fin n)
    (coefficient : Int) (hsource : source ∈ Set.range rows)
    (hdestination : destination ∈ Set.range rows) :
    ActsWithinRows rows
      (rowOperationMatrix (.add source destination coefficient)) := by
  classical
  constructor
  · intro row hrow column hcolumn
    by_cases hdestinationRow : row = destination
    · subst row
      have destination_ne : destination ≠ column := fun equality =>
        hcolumn (equality ▸ hdestination)
      have source_ne : source ≠ column := fun equality =>
        hcolumn (equality ▸ hsource)
      simp [rowOperationMatrix, destination_ne, source_ne]
    · rw [show rowOperationMatrix
          (.add source destination coefficient) row column =
            (1 : _root_.Matrix (Fin n) (Fin n) Int) row column by
        simp [rowOperationMatrix, hdestinationRow]]
      have hne : row ≠ column := fun equality => hcolumn (equality ▸ hrow)
      simp [hne]
  · intro row hrow column
    have hdestinationRow : row ≠ destination := fun equality =>
      hrow (equality ▸ hdestination)
    rw [show rowOperationMatrix
        (.add source destination coefficient) row column =
          (1 : _root_.Matrix (Fin n) (Fin n) Int) row column by
      simp [rowOperationMatrix, hdestinationRow]]
    rfl

theorem rowScaleMatrix_actsWithinRows {n r : Nat}
    {rows : Fin r ↪ Fin n} (row : Fin n) (coefficient : Int)
    (hrow : row ∈ Set.range rows) :
    ActsWithinRows rows (rowScaleMatrix row coefficient) := by
  classical
  constructor
  · intro current hcurrent column hcolumn
    by_cases equality : current = row
    · subst current
      have hne : row ≠ column := fun equality => hcolumn (equality ▸ hrow)
      simp [rowScaleMatrix, hne]
    · rw [show rowScaleMatrix row coefficient current column =
          (1 : _root_.Matrix (Fin n) (Fin n) Int) current column by
        simp [rowScaleMatrix, equality]]
      have hne : current ≠ column := fun same => hcolumn (same ▸ hcurrent)
      simp [hne]
  · intro current hcurrent column
    have hne : current ≠ row := fun equality => hcurrent (equality ▸ hrow)
    rw [show rowScaleMatrix row coefficient current column =
        (1 : _root_.Matrix (Fin n) (Fin n) Int) current column by
      simp [rowScaleMatrix, hne]]
    rfl

theorem State.actsWithinRows_gcdEliminate {n r : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} {rows : Fin r ↪ Fin n}
    (pivot target : Fin n) (hlt : pivot < target) (state : State A)
    (support : ActsWithinRows rows state.transform.U)
    (hpivot : pivot ∈ Set.range rows) (htarget : target ∈ Set.range rows) :
    ActsWithinRows rows (state.gcdEliminate pivot target hlt).transform.U := by
  change ActsWithinRows rows
    (boundedPairBezoutMatrix pivot target
      (state.transform.B pivot pivot) (state.transform.B target pivot) *
        state.transform.U)
  exact (twoRowLiftMatrix_actsWithinRows pivot target _ hpivot htarget hlt.ne).mul
    support

theorem State.actsWithinRows_reduceAbove {n r : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} {rows : Fin r ↪ Fin n}
    (source destination : Fin n) (hlt : source < destination)
    (state : State A) (support : ActsWithinRows rows state.transform.U)
    (hsource : source ∈ Set.range rows)
    (hdestination : destination ∈ Set.range rows) :
    ActsWithinRows rows (state.reduceAbove source destination hlt).transform.U := by
  change ActsWithinRows rows
    (rowOperationMatrix
        (.add destination source
          (-(ComputableEuclideanOps.quot
            (state.transform.B source destination)
            (state.transform.B destination destination)))) *
      state.transform.U)
  exact (rowAddMatrix_actsWithinRows destination source _
    hdestination hsource).mul support

theorem reduceAboveLoop_actsWithinRows {n r : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} {rows : Fin r ↪ Fin n}
    (destination : Fin n) (hdestination : destination ∈ Set.range rows) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      ActsWithinRows rows state.transform.U →
      (∀ row : Fin n, row.val < k → row ∈ Set.range rows) →
      ActsWithinRows rows
        (reduceAboveLoop destination k hk state).transform.U
  | 0, _, _, support, _ => support
  | k + 1, hk, state, support, hprefix => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have previousSupport := reduceAboveLoop_actsWithinRows destination
        hdestination k (by omega) state support (fun row hrow =>
          hprefix row (by omega))
      exact previous.actsWithinRows_reduceAbove source destination (by
        change k < destination.val
        omega) previousSupport (hprefix source (by
          dsimp [source]
          omega)) hdestination

theorem eliminateStageLoop_actsWithinRows {n r : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} {rows : Fin r ↪ Fin n}
    (target : Fin n) (htarget : target ∈ Set.range rows) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      ActsWithinRows rows state.transform.U →
      (∀ row : Fin n, row.val < k → row ∈ Set.range rows) →
      ActsWithinRows rows
        (eliminateStageLoop target k hk state).transform.U
  | 0, _, _, support, _ => support
  | k + 1, hk, state, support, hprefix => by
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      have previousSupport := eliminateStageLoop_actsWithinRows target htarget
        k (by omega) state support (fun row hrow => hprefix row (by omega))
      have hpivot : pivot ∈ Set.range rows := hprefix pivot (by
        dsimp [pivot]
        omega)
      let eliminated := previous.gcdEliminate pivot target (by
        change k < target.val
        omega)
      have eliminatedSupport := previous.actsWithinRows_gcdEliminate
        pivot target (by
          change k < target.val
          omega) previousSupport hpivot htarget
      exact reduceAboveLoop_actsWithinRows pivot hpivot pivot.val le_rfl
        eliminated eliminatedSupport (fun row hrow => hprefix row (by
          dsimp [pivot] at hrow
          omega))

/-- The first `processed` rows followed by the active target row. -/
def prefixTargetRows {n : Nat} (target : Fin n) (processed : Nat)
    (hprocessed : processed ≤ target.val) : Fin (processed + 1) ↪ Fin n :=
  let front : Fin processed ↪ Fin n :=
    Fin.castLEEmb (hprocessed.trans target.isLt.le)
  Fin.Embedding.snoc front (by
    rintro ⟨row, equality⟩
    have values := congrArg Fin.val equality
    change row.val = target.val at values
    omega)

@[simp] theorem prefixTargetRows_castSucc {n : Nat} (target : Fin n)
    (processed : Nat) (hprocessed : processed ≤ target.val)
    (row : Fin processed) :
    prefixTargetRows target processed hprocessed row.castSucc =
      Fin.castLE (hprocessed.trans target.isLt.le) row := by
  simp [prefixTargetRows, Fin.Embedding.snoc_castSucc]

@[simp] theorem prefixTargetRows_last {n : Nat} (target : Fin n)
    (processed : Nat) (hprocessed : processed ≤ target.val) :
    prefixTargetRows target processed hprocessed (Fin.last processed) =
      target := by
  simp [prefixTargetRows, Fin.Embedding.snoc_last]

theorem prefixTargetRows_target_mem {n : Nat} (target : Fin n)
    (processed : Nat) (hprocessed : processed ≤ target.val) :
    target ∈ Set.range (prefixTargetRows target processed hprocessed) :=
  ⟨Fin.last processed, prefixTargetRows_last target processed hprocessed⟩

theorem prefixTargetRows_prefix_mem {n : Nat} (target row : Fin n)
    (processed : Nat) (hprocessed : processed ≤ target.val)
    (hrow : row.val < processed) :
    row ∈ Set.range (prefixTargetRows target processed hprocessed) := by
  let source : Fin processed := ⟨row.val, hrow⟩
  refine ⟨source.castSucc, ?_⟩
  rw [prefixTargetRows_castSucc]
  exact Fin.ext rfl

/-- The first `processed` columns followed by one extra selected column. -/
def prefixExtraColumns {n : Nat} (column : Fin n) (processed : Nat)
    (hcolumn : processed ≤ column.val) : Fin (processed + 1) ↪ Fin n :=
  let front : Fin processed ↪ Fin n :=
    Fin.castLEEmb (hcolumn.trans column.isLt.le)
  Fin.Embedding.snoc front (by
    rintro ⟨index, equality⟩
    have values := congrArg Fin.val equality
    change index.val = column.val at values
    omega)

@[simp] theorem prefixExtraColumns_castSucc {n : Nat} (column : Fin n)
    (processed : Nat) (hcolumn : processed ≤ column.val)
    (index : Fin processed) :
    prefixExtraColumns column processed hcolumn index.castSucc =
      Fin.castLE (hcolumn.trans column.isLt.le) index := by
  simp [prefixExtraColumns, Fin.Embedding.snoc_castSucc]

@[simp] theorem prefixExtraColumns_last {n : Nat} (column : Fin n)
    (processed : Nat) (hcolumn : processed ≤ column.val) :
    prefixExtraColumns column processed hcolumn (Fin.last processed) =
      column := by
  simp [prefixExtraColumns, Fin.Embedding.snoc_last]

theorem eliminateStageLoop_refl_actsWithinRows {n : Nat}
    (B : _root_.Matrix (Fin n) (Fin n) Int) (target : Fin n)
    (processed : Nat) (hprocessed : processed ≤ target.val) :
    let rows := prefixTargetRows target processed hprocessed
    ActsWithinRows rows
      (eliminateStageLoop target processed hprocessed (State.refl B)).transform.U := by
  let rows := prefixTargetRows target processed hprocessed
  exact eliminateStageLoop_actsWithinRows target
    (prefixTargetRows_target_mem target processed hprocessed)
    processed hprocessed (State.refl B) (ActsWithinRows.one rows)
    (fun row hrow =>
      prefixTargetRows_prefix_mem target row processed hprocessed hrow)

theorem eliminateStageLoop_refl_selected_det_natAbs_eq {n : Nat}
    (B : _root_.Matrix (Fin n) (Fin n) Int) (target : Fin n)
    (processed : Nat) (hprocessed : processed ≤ target.val)
    (columns : Fin (processed + 1) → Fin n) :
    let rows := prefixTargetRows target processed hprocessed
    let eliminated :=
      eliminateStageLoop target processed hprocessed (State.refl B)
    (eliminated.transform.B.submatrix rows columns).det.natAbs =
      (B.submatrix rows columns).det.natAbs := by
  let rows := prefixTargetRows target processed hprocessed
  let eliminated := eliminateStageLoop target processed hprocessed (State.refl B)
  have support : ActsWithinRows rows eliminated.transform.U :=
    eliminateStageLoop_refl_actsWithinRows B target processed hprocessed
  let selectedU := eliminated.transform.U.submatrix rows rows
  let selectedB := B.submatrix rows columns
  let selectedResult := eliminated.transform.B.submatrix rows columns
  have equation : selectedU * selectedB = selectedResult :=
    eliminated.transform.selectedSubmatrix_equation rows columns support
  have unitDet : IsUnit selectedU.det :=
    (selectedSubmatrixCertificate rows support eliminated.transform.U_cert).unimodular
  change selectedResult.det.natAbs = selectedB.det.natAbs
  calc
    selectedResult.det.natAbs = (selectedU * selectedB).det.natAbs := by
      rw [equation]
    _ = selectedU.det.natAbs * selectedB.det.natAbs := by
      rw [_root_.Matrix.det_mul, Int.natAbs_mul]
    _ = selectedB.det.natAbs := by
      rw [Int.isUnit_iff_natAbs_eq.mp unitDet, one_mul]

theorem det_eq_last_entry_mul_of_last_row_zero {p : Nat}
    (M : _root_.Matrix (Fin (p + 1)) (Fin (p + 1)) Int)
    (lastZero : ∀ column : Fin p, M (Fin.last p) column.castSucc = 0) :
    M.det = M (Fin.last p) (Fin.last p) *
      (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [_root_.Matrix.det_succ_row M (Fin.last p)]
  rw [Finset.sum_eq_single (Fin.last p)]
  · simp only [Fin.val_last, Fin.succAbove_last]
    rw [Even.neg_one_pow (by exact ⟨p, by omega⟩ : Even (p + p))]
    simp
  · intro column _ hne
    have hlt : column.val < p := by
      exact (Fin.lt_last_iff_ne_last.mpr hne)
    let previous : Fin p := ⟨column.val, hlt⟩
    have equality : column = previous.castSucc := Fin.ext rfl
    rw [show M (Fin.last p) column = 0 by
      rw [equality]
      exact lastZero previous]
    ring
  · simp

theorem PrefixHermite.det_ne_of_diagonal_ne {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (hprefix : PrefixHermite n A)
    (diagonal_ne : ∀ row, A row row ≠ 0) :
    A.det ≠ 0 := by
  have upper : A.BlockTriangular id := by
    intro row column hcolumn
    exact hprefix.below row column row.isLt hcolumn
  rw [_root_.Matrix.det_of_upperTriangular upper]
  exact Finset.prod_ne_zero_iff.mpr fun row _ => diagonal_ne row

theorem reduceAboveLoop_apply_before {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      (pivotZero : ∀ column, column < destination →
        state.transform.B destination column = 0) →
      (row column : Fin n) → column < destination →
      (reduceAboveLoop destination k hk state).transform.B row column =
        state.transform.B row column
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, hk, state, pivotZero, row, column, hcolumn => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have hsource : source < destination := by
        change k < destination.val
        omega
      have previousZero : ∀ current, current < destination →
          previous.transform.B destination current = 0 := by
        intro current hcurrent
        rw [reduceAboveLoop_row_unchanged destination k (by omega) state
          destination current (by omega)]
        exact pivotZero current hcurrent
      change
        (previous.reduceAbove source destination hsource).transform.B
            row column = state.transform.B row column
      rw [State.reduceAbove_apply_before source destination hsource
        previous previousZero row column hcolumn]
      exact reduceAboveLoop_apply_before destination k (by omega) state
        pivotZero row column hcolumn

theorem eliminateStageLoop_diagonal_ne {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      PrefixHermite target.val state.transform.B →
      (∀ row, row.val < target.val → state.transform.B row row ≠ 0) →
      ∀ row, row.val < target.val →
        (eliminateStageLoop target k hk state).transform.B row row ≠ 0
  | 0, _, _, _, diagonal_ne => diagonal_ne
  | k + 1, hk, state, leading, diagonal_ne => by
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      have hpivot : pivot < target := by
        change k < target.val
        omega
      have previousInvariant := eliminateStageLoop_invariant target k
        (by omega) state leading
      have previousDiagonalNe := eliminateStageLoop_diagonal_ne target k
        (by omega) state leading diagonal_ne
      let eliminated := previous.gcdEliminate pivot target hpivot
      have pivotBefore : ∀ column, column < pivot →
          previous.transform.B pivot column = 0 := by
        intro column hcolumn
        exact previousInvariant.futureBelow pivot (by
          change k ≤ k
          omega) hpivot column hcolumn
      have targetBefore : ∀ column, column < pivot →
          previous.transform.B target column = 0 := by
        intro column hcolumn
        exact previousInvariant.targetZero column hcolumn
      have eliminatedPivotZero : ∀ column, column < pivot →
          eliminated.transform.B pivot column = 0 := by
        intro column hcolumn
        rw [State.gcdEliminate_pivot_apply]
        simp [pivotBefore column hcolumn, targetBefore column hcolumn]
      have eliminatedPivotNe : eliminated.transform.B pivot pivot ≠ 0 := by
        change (pairBezoutAt pivot target hpivot previous.transform).B pivot pivot ≠ 0
        rw [pairBezoutAt_pivot_pivot]
        intro gcd_zero
        have bothZero := (boundedIntXGCD_gcd_eq_zero_iff
          (previous.transform.B pivot pivot)
          (previous.transform.B target pivot)).1 gcd_zero
        exact previousDiagonalNe pivot (by omega) bothZero.1
      have eliminatedDiagonalNe : ∀ row, row.val < target.val →
          eliminated.transform.B row row ≠ 0 := by
        intro row hrow
        by_cases hp : row = pivot
        · subst row
          exact eliminatedPivotNe
        · have ht : row ≠ target := by
            intro equality
            subst row
            omega
          rw [State.gcdEliminate_other_apply pivot target row hpivot hp ht]
          exact previousDiagonalNe row hrow
      intro row hrow
      change
        (reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.B row row ≠ 0
      by_cases hbefore : row < pivot
      · rw [reduceAboveLoop_apply_before pivot pivot.val le_rfl eliminated
          eliminatedPivotZero row row hbefore]
        exact eliminatedDiagonalNe row hrow
      · rw [reduceAboveLoop_row_unchanged pivot pivot.val le_rfl eliminated
          row row (by omega)]
        exact eliminatedDiagonalNe row hrow

theorem State.gcdEliminate_B_congr {n : Nat}
    {A C : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target)
    (left : State A) (right : State C)
    (equal : left.transform.B = right.transform.B) :
    (left.gcdEliminate pivot target hlt).transform.B =
      (right.gcdEliminate pivot target hlt).transform.B := by
  simp only [State.gcdEliminate, pairBezoutAt, Transform.trans,
    Transform.ofPrimitive]
  rw [equal]

theorem State.reduceAbove_B_congr {n : Nat}
    {A C : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    (left : State A) (right : State C)
    (equal : left.transform.B = right.transform.B) :
    (left.reduceAbove source destination hlt).transform.B =
      (right.reduceAbove source destination hlt).transform.B := by
  simp only [State.reduceAbove, Transform.trans, Transform.add,
    Transform.ofPrimitive]
  rw [equal]

theorem reduceAboveLoop_B_congr {n : Nat}
    {A C : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) :
    (k : Nat) → (hk : k ≤ destination.val) →
      (left : State A) → (right : State C) →
      left.transform.B = right.transform.B →
      (reduceAboveLoop destination k hk left).transform.B =
        (reduceAboveLoop destination k hk right).transform.B
  | 0, _, _, _, equal => equal
  | k + 1, hk, left, right, equal => by
      let previousLeft := reduceAboveLoop destination k (by omega) left
      let previousRight := reduceAboveLoop destination k (by omega) right
      let source : Fin n := ⟨k, by omega⟩
      have hsource : source < destination := by
        change k < destination.val
        omega
      have previousEqual := reduceAboveLoop_B_congr destination k (by omega)
        left right equal
      change
        (previousLeft.reduceAbove source destination hsource).transform.B =
          (previousRight.reduceAbove source destination hsource).transform.B
      exact State.reduceAbove_B_congr source destination hsource previousLeft
        previousRight previousEqual

theorem eliminateStageLoop_B_congr {n : Nat}
    {A C : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) →
      (left : State A) → (right : State C) →
      left.transform.B = right.transform.B →
      (eliminateStageLoop target k hk left).transform.B =
        (eliminateStageLoop target k hk right).transform.B
  | 0, _, _, _, equal => equal
  | k + 1, hk, left, right, equal => by
      let previousLeft := eliminateStageLoop target k (by omega) left
      let previousRight := eliminateStageLoop target k (by omega) right
      let pivot : Fin n := ⟨k, by omega⟩
      have hpivot : pivot < target := by
        change k < target.val
        omega
      have previousEqual := eliminateStageLoop_B_congr target k (by omega)
        left right equal
      let eliminatedLeft := previousLeft.gcdEliminate pivot target hpivot
      let eliminatedRight := previousRight.gcdEliminate pivot target hpivot
      have eliminatedEqual : eliminatedLeft.transform.B =
          eliminatedRight.transform.B :=
        State.gcdEliminate_B_congr pivot target hpivot previousLeft
          previousRight previousEqual
      change
        (reduceAboveLoop pivot pivot.val le_rfl eliminatedLeft).transform.B =
          (reduceAboveLoop pivot pivot.val le_rfl eliminatedRight).transform.B
      exact reduceAboveLoop_B_congr pivot pivot.val le_rfl eliminatedLeft
        eliminatedRight eliminatedEqual

theorem eliminateStageLoop_B_eq_refl {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (k : Nat) (hk : k ≤ target.val) (state : State A) :
    (eliminateStageLoop target k hk state).transform.B =
      (eliminateStageLoop target k hk
        (State.refl state.transform.B)).transform.B :=
  eliminateStageLoop_B_congr target k hk state
    (State.refl state.transform.B) rfl

theorem eliminateStageLoop_row_unchanged {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      (row column : Fin n) → k ≤ row.val → row ≠ target →
      (eliminateStageLoop target k hk state).transform.B row column =
        state.transform.B row column
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, hk, state, row, column, hrow, htarget => by
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      have hpivot : pivot < target := by
        change k < target.val
        omega
      have row_ne_pivot : row ≠ pivot := by
        intro equality
        have values := congrArg Fin.val equality
        dsimp [pivot] at values
        omega
      let eliminated := previous.gcdEliminate pivot target hpivot
      change
        (reduceAboveLoop pivot pivot.val le_rfl eliminated).transform.B
            row column = state.transform.B row column
      rw [reduceAboveLoop_row_unchanged pivot pivot.val le_rfl eliminated
        row column (by dsimp [pivot]; omega)]
      rw [State.gcdEliminate_other_apply pivot target row hpivot
        row_ne_pivot htarget]
      exact eliminateStageLoop_row_unchanged target k (by omega) state
        row column (by omega) htarget

theorem eliminateStageLoop_refl_target_entry_natAbs_le {n : Nat}
    (B : _root_.Matrix (Fin n) (Fin n) Int) (target : Fin n)
    (processed : Nat) (hprocessed : processed ≤ target.val)
    (leading : PrefixHermite target.val B)
    (diagonal_ne : ∀ row, row.val < target.val → B row row ≠ 0)
    (column : Fin n) (hcolumn : processed ≤ column.val) :
    let eliminated :=
      eliminateStageLoop target processed hprocessed (State.refl B)
    eliminated.transform.B target column |>.natAbs ≤
      (processed + 1).factorial * matrixHeight B ^ (processed + 1) := by
  let eliminated :=
    eliminateStageLoop target processed hprocessed (State.refl B)
  let rows := prefixTargetRows target processed hprocessed
  let columns := prefixExtraColumns column processed hcolumn
  let selected := eliminated.transform.B.submatrix rows columns
  have hn : processed ≤ n := hprocessed.trans target.isLt.le
  have invariant : EliminationInvariant target processed eliminated :=
    eliminateStageLoop_invariant target processed hprocessed (State.refl B) leading
  have resultingDiagonalNe : ∀ row, row.val < target.val →
      eliminated.transform.B row row ≠ 0 :=
    eliminateStageLoop_diagonal_ne target processed hprocessed (State.refl B)
      leading diagonal_ne
  have lastZero : ∀ previous : Fin processed,
      selected (Fin.last processed) previous.castSucc = 0 := by
    intro previous
    change eliminated.transform.B
      (rows (Fin.last processed)) (columns previous.castSucc) = 0
    rw [prefixTargetRows_last, prefixExtraColumns_castSucc]
    exact invariant.targetZero _ (by simp)
  have topLeft :
      selected.submatrix Fin.castSucc Fin.castSucc =
        leadingSubmatrix hn eliminated.transform.B := by
    ext row col
    simp [selected, rows, columns, leadingSubmatrix]
  have leadingDiagonalNe : ∀ row : Fin processed,
      leadingSubmatrix hn eliminated.transform.B row row ≠ 0 := by
    intro row
    change eliminated.transform.B (Fin.castLE hn row) (Fin.castLE hn row) ≠ 0
    exact resultingDiagonalNe _ (by simp; omega)
  have leadingDetNe :
      (selected.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
    rw [topLeft]
    exact (invariant.leading.leadingSubmatrix hn).det_ne_of_diagonal_ne
      leadingDiagonalNe
  have factor := det_eq_last_entry_mul_of_last_row_zero selected lastZero
  have selectedLast :
      selected (Fin.last processed) (Fin.last processed) =
        eliminated.transform.B target column := by
    simp [selected, rows, columns]
  calc
    (eliminated.transform.B target column).natAbs =
        (selected (Fin.last processed) (Fin.last processed)).natAbs := by
      rw [selectedLast]
    _ ≤ (selected (Fin.last processed) (Fin.last processed)).natAbs *
          (selected.submatrix Fin.castSucc Fin.castSucc).det.natAbs :=
      Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr leadingDetNe)
    _ = selected.det.natAbs := by
      rw [factor, Int.natAbs_mul]
    _ = (B.submatrix rows columns).det.natAbs :=
      eliminateStageLoop_refl_selected_det_natAbs_eq B target processed
        hprocessed columns
    _ ≤ (processed + 1).factorial * matrixHeight B ^ (processed + 1) :=
      minor_natAbs_le_height_factorial B rows columns

theorem eliminateStageLoop_target_entry_natAbs_le {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (processed : Nat)
    (hprocessed : processed ≤ target.val) (state : State A)
    (leading : PrefixHermite target.val state.transform.B)
    (diagonal_ne : ∀ row, row.val < target.val →
      state.transform.B row row ≠ 0)
    (column : Fin n) (hcolumn : processed ≤ column.val) :
    ((eliminateStageLoop target processed hprocessed state).transform.B
        target column).natAbs ≤
      (processed + 1).factorial *
        matrixHeight state.transform.B ^ (processed + 1) := by
  have equal := eliminateStageLoop_B_eq_refl target processed hprocessed state
  rw [equal]
  exact eliminateStageLoop_refl_target_entry_natAbs_le state.transform.B
    target processed hprocessed leading diagonal_ne column hcolumn

end Principal

end NormalForms.Research.KannanBachem.Hermite
