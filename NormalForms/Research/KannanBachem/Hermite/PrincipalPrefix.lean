/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
import all NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal

/-! Row-prefix support for the principal-minor schedule. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix BigOperators
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

namespace Principal

/-- The leading square submatrix selected by the canonical `Fin` embedding. -/
@[expose] public def leadingSubmatrix {n k : Nat} (hk : k ≤ n)
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    _root_.Matrix (Fin k) (Fin k) Int :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

theorem sum_castLE_eq_of_outside_zero {n k : Nat} (hk : k ≤ n)
    (f : Fin n → Int) (outside : ∀ index, k ≤ index.val → f index = 0) :
    (∑ index : Fin k, f (Fin.castLE hk index)) =
      ∑ index : Fin n, f index := by
  classical
  let embedding : Fin k ↪ Fin n := Fin.castLEEmb hk
  calc
    (∑ index : Fin k, f (Fin.castLE hk index)) =
        Finset.sum (Finset.univ.map embedding) f := by
      rw [Finset.sum_map]
      rfl
    _ = Finset.sum Finset.univ f := by
      apply Finset.sum_subset
      · exact Finset.subset_univ _
      · intro index _ hnot
        apply outside index
        by_contra hlt
        apply hnot
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        refine ⟨⟨index.val, by omega⟩, ?_⟩
        exact Fin.ext rfl

/-- A square matrix is the identity outside its leading `bound` rows and columns. -/
def ActsWithinPrefix {n : Nat} (bound : Nat)
    (U : _root_.Matrix (Fin n) (Fin n) Int) : Prop :=
  (∀ row column, row.val < bound → bound ≤ column.val → U row column = 0) ∧
  (∀ row column, bound ≤ row.val →
    U row column = if row = column then 1 else 0)

theorem ActsWithinPrefix.one {n bound : Nat} :
    ActsWithinPrefix bound
      (1 : _root_.Matrix (Fin n) (Fin n) Int) := by
  constructor
  · intro row column hrow hcolumn
    have hne : row ≠ column := by
      intro equality
      subst column
      omega
    simp [hne]
  · intro row column _
    rfl

theorem ActsWithinPrefix.mul {n bound : Nat}
    {U V : _root_.Matrix (Fin n) (Fin n) Int}
    (hU : ActsWithinPrefix bound U)
    (hV : ActsWithinPrefix bound V) :
    ActsWithinPrefix bound (U * V) := by
  constructor
  · intro row column hrow hcolumn
    rw [_root_.Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro middle _
    by_cases hmiddle : middle.val < bound
    · rw [hV.1 middle column hmiddle hcolumn, mul_zero]
    · rw [hU.1 row middle hrow (by omega), zero_mul]
  · intro row column hrow
    rw [_root_.Matrix.mul_apply]
    calc
      (∑ middle, U row middle * V middle column) =
          ∑ middle, (if row = middle then 1 else 0) * V middle column := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [hU.2 row middle hrow]
      _ = V row column := by simp
      _ = if row = column then 1 else 0 := hV.2 row column hrow

theorem ActsWithinPrefix.mono {n smaller larger : Nat}
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (hU : ActsWithinPrefix smaller U) (hle : smaller ≤ larger) :
    ActsWithinPrefix larger U := by
  constructor
  · intro row column hrow hcolumn
    by_cases hsmall : row.val < smaller
    · exact hU.1 row column hsmall (hle.trans hcolumn)
    · have hne : row ≠ column := by
        intro equality
        subst column
        omega
      rw [hU.2 row column (by omega), if_neg hne]
  · intro row column hrow
    exact hU.2 row column (hle.trans hrow)

theorem ActsWithinPrefix.leadingSubmatrix_mul {n k : Nat} (hk : k ≤ n)
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (support : ActsWithinPrefix k U)
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    leadingSubmatrix hk U * leadingSubmatrix hk A =
      leadingSubmatrix hk (U * A) := by
  ext row column
  simp only [leadingSubmatrix, _root_.Matrix.submatrix_apply,
    _root_.Matrix.mul_apply]
  exact sum_castLE_eq_of_outside_zero hk
    (fun middle =>
      U (Fin.castLE hk row) middle * A middle (Fin.castLE hk column))
    (by
      intro middle hmiddle
      rw [support.1 (Fin.castLE hk row) middle row.isLt hmiddle, zero_mul])

theorem ActsWithinPrefix.inverse {n bound : Nat}
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (support : ActsWithinPrefix bound U)
    (certificate : MatrixInverseCertificate U) :
    ActsWithinPrefix bound certificate.inverse := by
  constructor
  · intro row column hrow hcolumn
    have row_ne_column : row ≠ column := by
      intro equality
      subst column
      omega
    have columnIdentity : ∀ middle,
        U middle column = if middle = column then 1 else 0 := by
      intro middle
      by_cases hmiddle : middle.val < bound
      · have middle_ne_column : middle ≠ column := by
          intro equality
          subst column
          omega
        rw [support.1 middle column hmiddle hcolumn, if_neg middle_ne_column]
      · exact support.2 middle column (by omega)
    have entry := congrFun (congrFun certificate.left_inv row) column
    rw [_root_.Matrix.mul_apply] at entry
    simp_rw [columnIdentity] at entry
    simpa [row_ne_column] using entry
  · intro row column hrow
    have entry := congrFun (congrFun certificate.right_inv row) column
    rw [_root_.Matrix.mul_apply] at entry
    simp_rw [support.2 row _ hrow] at entry
    change certificate.inverse row column =
      (1 : _root_.Matrix (Fin n) (Fin n) Int) row column
    simpa using entry

@[simp] theorem leadingSubmatrix_one {n k : Nat} (hk : k ≤ n) :
    leadingSubmatrix hk
        (1 : _root_.Matrix (Fin n) (Fin n) Int) =
      (1 : _root_.Matrix (Fin k) (Fin k) Int) := by
  ext row column
  change
    (1 : _root_.Matrix (Fin n) (Fin n) Int)
        (Fin.castLE hk row) (Fin.castLE hk column) =
      (1 : _root_.Matrix (Fin k) (Fin k) Int) row column
  simp only [_root_.Matrix.one_apply, Fin.castLE_inj]

def leadingSubmatrixCertificate {n k : Nat} (hk : k ≤ n)
    {U : _root_.Matrix (Fin n) (Fin n) Int}
    (support : ActsWithinPrefix k U)
    (certificate : MatrixInverseCertificate U) :
    MatrixInverseCertificate (leadingSubmatrix hk U) :=
  { inverse := leadingSubmatrix hk certificate.inverse
    left_inv := by
      rw [support.inverse certificate |>.leadingSubmatrix_mul hk,
        certificate.left_inv, leadingSubmatrix_one]
    right_inv := by
      rw [support.leadingSubmatrix_mul hk,
        certificate.right_inv, leadingSubmatrix_one] }

theorem Transform.leadingSubmatrix_equation {m n k : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int} (hk : k ≤ m)
    (transform : Transform A)
    (support : ActsWithinPrefix k transform.U) :
    leadingSubmatrix hk transform.U *
        A.submatrix (Fin.castLE hk) id =
      transform.B.submatrix (Fin.castLE hk) id := by
  ext row column
  simp only [leadingSubmatrix, _root_.Matrix.mul_apply,
    _root_.Matrix.submatrix_apply, id_eq]
  have equationEntry := congrFun
    (congrFun transform.equation (Fin.castLE hk row)) column
  rw [_root_.Matrix.mul_apply] at equationEntry
  rw [sum_castLE_eq_of_outside_zero hk
    (fun middle =>
      transform.U (Fin.castLE hk row) middle * A middle column)
    (by
      intro middle hmiddle
      rw [support.1 (Fin.castLE hk row) middle row.isLt hmiddle, zero_mul])]
  exact equationEntry

theorem Transform.leadingSquare_equation {n k : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (hk : k ≤ n)
    (transform : Transform A)
    (support : ActsWithinPrefix k transform.U) :
    leadingSubmatrix hk transform.U * leadingSubmatrix hk A =
      leadingSubmatrix hk transform.B := by
  calc
    leadingSubmatrix hk transform.U * leadingSubmatrix hk A =
        leadingSubmatrix hk (transform.U * A) :=
      support.leadingSubmatrix_mul hk A
    _ = leadingSubmatrix hk transform.B := by rw [transform.equation]

def Transform.leadingSubmatrixCertificate {n k : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (hk : k ≤ n)
    (transform : Transform A)
    (support : ActsWithinPrefix k transform.U) :
    MatrixInverseCertificate (leadingSubmatrix hk transform.U) :=
  Principal.leadingSubmatrixCertificate hk support transform.U_cert

theorem PrefixHermite.leadingSubmatrix {n k : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (hk : k ≤ n)
    (hprefix : PrefixHermite k A) :
    PrefixHermite k (leadingSubmatrix hk A) :=
  { diagonal := by
      intro row hrow
      change A (Fin.castLE hk row) (Fin.castLE hk row) =
        _root_.normalize (A (Fin.castLE hk row) (Fin.castLE hk row))
      exact hprefix.diagonal (Fin.castLE hk row) hrow
    below := by
      intro row column hrow hcolumn
      change A (Fin.castLE hk row) (Fin.castLE hk column) = 0
      exact hprefix.below (Fin.castLE hk row) (Fin.castLE hk column)
        hrow (by simpa using hcolumn)
    reduced := by
      intro row column hcolumn hrow
      change A (Fin.castLE hk row) (Fin.castLE hk column) =
        A (Fin.castLE hk row) (Fin.castLE hk column) %
          A (Fin.castLE hk column) (Fin.castLE hk column)
      exact hprefix.reduced (Fin.castLE hk row) (Fin.castLE hk column)
        hcolumn (by simpa using hrow) }

theorem PrefixHermite.diagonal_ne_of_det_ne {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (hprefix : PrefixHermite n A) (det_ne : A.det ≠ 0) :
    ∀ row, A row row ≠ 0 := by
  have upper : A.BlockTriangular id := by
    intro row column hcolumn
    exact hprefix.below row column row.isLt hcolumn
  have product_ne : (∏ row : Fin n, A row row) ≠ 0 := by
    rw [← _root_.Matrix.det_of_upperTriangular upper]
    exact det_ne
  exact fun row =>
    (Finset.prod_ne_zero_iff.mp product_ne) row (Finset.mem_univ row)

/-- Every canonical leading principal submatrix has nonzero determinant. -/
@[expose] public def PrincipalReady {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) : Prop :=
  ∀ (k : Nat) (hk : k ≤ n), (leadingSubmatrix hk A).det ≠ 0

theorem twoRowLiftMatrix_actsWithinPrefix {n bound : Nat}
    (pivot target : Fin n) (pair : _root_.Matrix (Fin 2) (Fin 2) Int)
    (hpivot : pivot.val < bound) (htarget : target.val < bound)
    (hne : pivot ≠ target) :
    ActsWithinPrefix bound (twoRowLiftMatrix pivot target pair) := by
  constructor
  · intro row column hrow hcolumn
    by_cases hp : row = pivot
    · subst row
      simp only [twoRowLiftMatrix_apply_pivot pivot target hne]
      have hpj : pivot ≠ column := by
        intro equality
        subst column
        omega
      have htj : target ≠ column := by
        intro equality
        subst column
        omega
      simp [hpj, htj]
    · by_cases ht : row = target
      · subst row
        simp only [twoRowLiftMatrix_apply_target]
        have hpj : pivot ≠ column := by
          intro equality
          subst column
          omega
        have htj : target ≠ column := by
          intro equality
          subst column
          omega
        simp [hpj, htj]
      · rw [twoRowLiftMatrix_apply_other pivot target row hp ht]
        have hne' : row ≠ column := by
          intro equality
          subst column
          omega
        simp [hne']
  · intro row column hrow
    have hp : row ≠ pivot := by
      intro equality
      subst row
      omega
    have ht : row ≠ target := by
      intro equality
      subst row
      omega
    rw [twoRowLiftMatrix_apply_other pivot target row hp ht]
    rfl

theorem rowAddMatrix_actsWithinPrefix {n bound : Nat}
    (source destination : Fin n) (coefficient : Int)
    (hsource : source.val < bound) (hdestination : destination.val < bound) :
    ActsWithinPrefix bound
      (rowOperationMatrix (.add source destination coefficient)) := by
  constructor
  · intro row column hrow hcolumn
    by_cases hrowDestination : row = destination
    · subst row
      have hdestinationColumn : destination ≠ column := by
        intro equality
        subst column
        omega
      have hsourceColumn : source ≠ column := by
        intro equality
        subst column
        omega
      simp [rowOperationMatrix, hdestinationColumn, hsourceColumn]
    · rw [show rowOperationMatrix
          (.add source destination coefficient) row column =
            (1 : _root_.Matrix (Fin n) (Fin n) Int) row column by
        simp [rowOperationMatrix, hrowDestination]]
      have hne : row ≠ column := by
        intro equality
        subst column
        omega
      simp [hne]
  · intro row column hrow
    have hrowDestination : row ≠ destination := by
      intro equality
      subst row
      omega
    rw [show rowOperationMatrix
        (.add source destination coefficient) row column =
          (1 : _root_.Matrix (Fin n) (Fin n) Int) row column by
      simp [rowOperationMatrix, hrowDestination]]
    rfl

theorem rowScaleMatrix_actsWithinPrefix {n bound : Nat}
    (row : Fin n) (coefficient : Int) (hrow : row.val < bound) :
    ActsWithinPrefix bound (rowScaleMatrix row coefficient) := by
  constructor
  · intro current column hcurrent hcolumn
    by_cases equality : current = row
    · subst current
      have hne : row ≠ column := by
        intro equality
        subst column
        omega
      simp [rowScaleMatrix, hne]
    · rw [show rowScaleMatrix row coefficient current column =
          (1 : _root_.Matrix (Fin n) (Fin n) Int) current column by
        simp [rowScaleMatrix, equality]]
      have hne : current ≠ column := by
        intro same
        subst column
        omega
      simp [hne]
  · intro current column hcurrent
    have hne : current ≠ row := by
      intro equality
      subst current
      omega
    rw [show rowScaleMatrix row coefficient current column =
        (1 : _root_.Matrix (Fin n) (Fin n) Int) current column by
      simp [rowScaleMatrix, hne]]
    rfl

theorem State.actsWithinPrefix_gcdEliminate {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (pivot target : Fin n) (hlt : pivot < target) (state : State A)
    (support : ActsWithinPrefix bound state.transform.U)
    (hpivot : pivot.val < bound) (htarget : target.val < bound) :
    ActsWithinPrefix bound
      (state.gcdEliminate pivot target hlt).transform.U := by
  change ActsWithinPrefix bound
    (boundedPairBezoutMatrix pivot target
      (state.transform.B pivot pivot) (state.transform.B target pivot) *
        state.transform.U)
  apply ActsWithinPrefix.mul
  · exact twoRowLiftMatrix_actsWithinPrefix pivot target _
      hpivot htarget hlt.ne
  · exact support

theorem State.actsWithinPrefix_reduceAbove {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (source destination : Fin n) (hlt : source < destination)
    (state : State A) (support : ActsWithinPrefix bound state.transform.U)
    (hsource : source.val < bound) (hdestination : destination.val < bound) :
    ActsWithinPrefix bound
      (state.reduceAbove source destination hlt).transform.U := by
  change ActsWithinPrefix bound
    (rowOperationMatrix
        (.add destination source
          (-(ComputableEuclideanOps.quot
            (state.transform.B source destination)
            (state.transform.B destination destination)))) *
      state.transform.U)
  exact (rowAddMatrix_actsWithinPrefix destination source _
    hdestination hsource).mul support

theorem State.actsWithinPrefix_normalize {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (row : Fin n) (state : State A)
    (support : ActsWithinPrefix bound state.transform.U)
    (hrow : row.val < bound) :
    ActsWithinPrefix bound (state.normalize row).transform.U := by
  change ActsWithinPrefix bound
    (rowScaleMatrix row
        (ComputableEuclideanOps.normUnitUnit
          (state.transform.B row row) : Int) * state.transform.U)
  exact (rowScaleMatrix_actsWithinPrefix row _ hrow).mul support

theorem reduceAboveLoop_actsWithinPrefix {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (destination : Fin n) (hdestination : destination.val < bound) :
    (k : Nat) → (hk : k ≤ destination.val) → (state : State A) →
      ActsWithinPrefix bound state.transform.U →
      ActsWithinPrefix bound
        (reduceAboveLoop destination k hk state).transform.U
  | 0, _, _, support => support
  | k + 1, hk, state, support => by
      let previous := reduceAboveLoop destination k (by omega) state
      let source : Fin n := ⟨k, by omega⟩
      have previousSupport := reduceAboveLoop_actsWithinPrefix destination
        hdestination k (by omega) state support
      exact previous.actsWithinPrefix_reduceAbove source destination (by
        change k < destination.val
        omega) previousSupport (by
          dsimp [source]
          omega) hdestination

theorem eliminateStageLoop_actsWithinPrefix {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (htarget : target.val < bound) :
    (k : Nat) → (hk : k ≤ target.val) → (state : State A) →
      ActsWithinPrefix bound state.transform.U →
      ActsWithinPrefix bound
        (eliminateStageLoop target k hk state).transform.U
  | 0, _, _, support => support
  | k + 1, hk, state, support => by
      let previous := eliminateStageLoop target k (by omega) state
      let pivot : Fin n := ⟨k, by omega⟩
      have previousSupport := eliminateStageLoop_actsWithinPrefix target
        htarget k (by omega) state support
      let eliminated := previous.gcdEliminate pivot target (by
        change k < target.val
        omega)
      have eliminatedSupport := previous.actsWithinPrefix_gcdEliminate
        pivot target (by
          change k < target.val
          omega) previousSupport (by
            dsimp [pivot]
            omega) htarget
      exact reduceAboveLoop_actsWithinPrefix pivot (by
        dsimp [pivot]
        omega) pivot.val le_rfl eliminated eliminatedSupport

theorem extendStage_actsWithinPrefix {n bound : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    (target : Fin n) (htarget : target.val < bound) (state : State A)
    (support : ActsWithinPrefix bound state.transform.U) :
    ActsWithinPrefix bound (extendStage target state).transform.U := by
  let eliminated := eliminateStageLoop target target.val le_rfl state
  have eliminatedSupport := eliminateStageLoop_actsWithinPrefix target htarget
    target.val le_rfl state support
  let normalized := eliminated.normalize target
  have normalizedSupport := eliminated.actsWithinPrefix_normalize target
    eliminatedSupport htarget
  exact reduceAboveLoop_actsWithinPrefix target htarget target.val le_rfl
    normalized normalizedSupport

theorem stageLoop_actsWithinPrefix {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : State A) →
      ActsWithinPrefix 0 state.transform.U →
      ActsWithinPrefix k (stageLoop k hk state).transform.U
  | 0, _, _, support => support
  | k + 1, hk, state, support => by
      let previous := stageLoop k (by omega) state
      have previousSupport := stageLoop_actsWithinPrefix k (by omega) state support
      let target : Fin n := ⟨k, by omega⟩
      have htarget : target.val < k + 1 := by simp [target]
      exact extendStage_actsWithinPrefix target htarget previous
        (previousSupport.mono (by omega))

theorem stageLoop_refl_actsWithinPrefix {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n) :
    ActsWithinPrefix k
      (stageLoop k hk (State.refl A)).transform.U :=
  stageLoop_actsWithinPrefix k hk (State.refl A) ActsWithinPrefix.one

theorem stageLoop_refl_leadingSquare_equation {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n) :
    leadingSubmatrix hk
          (stageLoop k hk (State.refl A)).transform.U *
        leadingSubmatrix hk A =
      leadingSubmatrix hk
        (stageLoop k hk (State.refl A)).transform.B :=
  (stageLoop k hk (State.refl A)).transform.leadingSquare_equation hk
    (stageLoop_refl_actsWithinPrefix A hk)

theorem stageLoop_refl_leading_det_ne {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (ready : PrincipalReady A) :
    (leadingSubmatrix hk
      (stageLoop k hk (State.refl A)).transform.B).det ≠ 0 := by
  rw [← stageLoop_refl_leadingSquare_equation A hk, _root_.Matrix.det_mul]
  exact mul_ne_zero
    (_root_.Matrix.det_ne_zero_of_left_inverse
      ((stageLoop k hk (State.refl A)).transform.leadingSubmatrixCertificate
        hk (stageLoop_refl_actsWithinPrefix A hk)).left_inv)
    (ready k hk)

theorem stageLoop_refl_leading_prefix {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n) :
    PrefixHermite k
      (leadingSubmatrix hk
        (stageLoop k hk (State.refl A)).transform.B) :=
  (stageLoop_correct k hk (State.refl A)).leadingSubmatrix hk

theorem Transform.row_eq_input_of_actsWithinPrefix {m n bound : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int} (transform : Transform A)
    (support : ActsWithinPrefix bound transform.U)
    (row : Fin m) (hrow : bound ≤ row.val) (column : Fin n) :
    transform.B row column = A row column := by
  rw [← transform.equation, _root_.Matrix.mul_apply]
  calc
    (∑ middle, transform.U row middle * A middle column) =
        ∑ middle, (if row = middle then 1 else 0) * A middle column := by
      apply Finset.sum_congr rfl
      intro middle _
      rw [support.2 row middle hrow]
    _ = A row column := by simp

/-- Rows not yet admitted to the principal prefix are byte-for-byte input rows. -/
theorem stageLoop_refl_unprocessed_row {n k : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hk : k ≤ n)
    (row column : Fin n) (hrow : k ≤ row.val) :
    (stageLoop k hk (State.refl A)).transform.B row column =
      A row column :=
  (stageLoop k hk (State.refl A)).transform.row_eq_input_of_actsWithinPrefix
    (stageLoop_refl_actsWithinPrefix A hk) row hrow column

end Principal

end NormalForms.Research.KannanBachem.Hermite
