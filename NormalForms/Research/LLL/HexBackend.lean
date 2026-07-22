/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import HexLLLMathlib
public import NormalForms.Matrix.Elementary.Basic

/-!
# Dense verified backend for the LLL research profile

The executable integer reducer and its termination proof come from the pinned
`hex-lll-mathlib` package.  This module is the only representation boundary:
the rest of the profile continues to expose Mathlib matrices and the project's
explicit inverse certificates.
-/

@[expose] public section

namespace NormalForms.Research.LLL

open NormalForms.Matrix.Elementary

/-- Convert a Mathlib matrix to the dense executable representation. -/
public def toDense {m n : Nat} (basis : Matrix (Fin m) (Fin n) Int) :
    Hex.Matrix Int m n :=
  HexMatrixMathlib.matrixEquiv.symm basis

/-- Convert a dense executable matrix back to Mathlib's function representation. -/
public def ofDense {m n : Nat} (basis : Hex.Matrix Int m n) :
    Matrix (Fin m) (Fin n) Int :=
  HexMatrixMathlib.matrixEquiv basis

@[simp] public theorem ofDense_toDense {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) :
    ofDense (toDense basis) = basis :=
  HexMatrixMathlib.matrixEquiv.apply_symm_apply basis

@[simp] public theorem toDense_ofDense {m n : Nat}
    (basis : Hex.Matrix Int m n) :
    toDense (ofDense basis) = basis :=
  HexMatrixMathlib.matrixEquiv.symm_apply_apply basis

/-- Dense row addition agrees entrywise with the project's row-operation semantics. -/
public theorem ofDense_rowAdd {m n : Nat} (basis : Hex.Matrix Int m n)
    (source target : Fin m) (coefficient : Int) :
  ofDense (Hex.Matrix.rowAdd basis source target coefficient) =
      applyRowOperation (ofDense basis) (.add source target coefficient) := by
  ext row column
  change (Hex.Matrix.rowAdd basis source target coefficient)[row][column] = _
  rw [Hex.Matrix.getElem_rowAdd]
  by_cases atTarget : row = target
  · subst row
    simp [ofDense, applyRowOperation]
  · simp [ofDense, applyRowOperation, atTarget]

/-- Dense row swaps agree entrywise with the project's row-operation semantics. -/
public theorem ofDense_rowSwap {m n : Nat} (basis : Hex.Matrix Int m n)
    (left right : Fin m) :
  ofDense (Hex.Matrix.rowSwap basis left right) =
      applyRowOperation (ofDense basis) (.swap left right) := by
  ext row column
  change (Hex.Matrix.rowSwap basis left right)[row][column] = _
  rw [Hex.Matrix.getElem_rowSwap]
  by_cases atLeft : row = left
  · subst row
    by_cases equal : left = right
    · subst right
      simp [ofDense, applyRowOperation]
    · simp [ofDense, applyRowOperation, equal]
  · by_cases atRight : row = right
    · subst row
      simp [ofDense, applyRowOperation, atLeft]
    · simp [ofDense, applyRowOperation, atLeft, atRight]

/-- The verified dense native reducer at the profile's fixed parameters. -/
public def denseLLL {m n : Nat} (basis : Matrix (Fin m) (Fin n) Int)
    (rowsPositive : 1 <= m) : Matrix (Fin m) (Fin n) Int :=
  ofDense (Hex.lllNative (toDense basis) (3 / 4) (by grind) (by grind) rowsPositive)

/-- Row-lattice containment produces a Mathlib-side integer row transform. -/
public theorem exists_leftTransform_of_memLattice {m n : Nat}
    (source target : Hex.Matrix Int m n)
    (contained : ∀ vector, target.memLattice vector → source.memLattice vector) :
    ∃ U : Matrix (Fin m) (Fin m) Int, U * ofDense source = ofDense target := by
  classical
  have rowCombination : ∀ row : Fin m,
      ∃ coefficients : Vector Int m,
        Hex.Matrix.vecMul coefficients source = Hex.Matrix.row target row := by
    intro row
    have rowMem : target.memLattice (Hex.Matrix.row target row) :=
      (HexLLLMathlib.mem_latticeSubmodule_iff target _).mp
        (HexLLLMathlib.row_mem_latticeSubmodule target row)
    exact contained _ rowMem
  choose coefficients equation using rowCombination
  let U : Matrix (Fin m) (Fin m) Int :=
    fun row column => HexMatrixMathlib.vectorEquiv (coefficients row) column
  refine ⟨U, ?_⟩
  ext row column
  have rowEquation := congrArg HexMatrixMathlib.vectorEquiv (equation row)
  have entryEquation := congrFun rowEquation column
  rw [HexMatrixMathlib.vectorEquiv_vecMul] at entryEquation
  simpa [U, Matrix.mul_apply, Fintype.linearCombination_apply,
    ofDense, Matrix.row, Hex.Matrix.row, mul_comm] using entryEquation

/-- Equal dense row lattices yield explicit transforms in both directions. -/
public theorem exists_mutualLeftTransforms_of_memLattice_iff {m n : Nat}
    (left right : Hex.Matrix Int m n)
    (sameLattice : ∀ vector, left.memLattice vector ↔ right.memLattice vector) :
    ∃ U V : Matrix (Fin m) (Fin m) Int,
      U * ofDense left = ofDense right ∧ V * ofDense right = ofDense left := by
  obtain ⟨U, hU⟩ := exists_leftTransform_of_memLattice left right
    (fun vector => (sameLattice vector).mpr)
  obtain ⟨V, hV⟩ := exists_leftTransform_of_memLattice right left
    (fun vector => (sameLattice vector).mp)
  exact ⟨U, V, hU, hV⟩

end NormalForms.Research.LLL
