/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Result
import all NormalForms.Research.LLL.Internal.HexTrace
import all NormalForms.Research.LLL.Internal.PrefixLift
import all NormalForms.Research.LLL.Internal.RankDecomposition

/-!
# Total integer LLL

The row entry accepts empty, dependent, and zero-row inputs.  It first obtains
a certified unimodular Hermite rank decomposition, reduces the independent
prefix, then lifts and composes the prefix transform.  The column entry is only
the transpose adapter required by the fixed row-basis convention.
-/

@[expose] public section

namespace NormalForms.Research.LLL

open scoped Matrix
open NormalForms.Matrix.Certificates
open Internal.PrefixLift
open Internal.RankDecomposition

private theorem emptyRowsReduced {columns : Nat}
    (basis : Matrix (Fin 0) (Fin columns) Int) : IsLLLReduced basis := by
  refine
    { positive := ?_
      sizeReduced := ?_
      lovasz := ?_ }
  · intro row
    exact Fin.elim0 row
  · intro row column row_lt column_lt
    omega
  · intro row row_lt
    omega

private def reduceIndependentPrefix {rows columns : Nat}
    (basis : Matrix (Fin rows) (Fin columns) Int)
    (fullRank : FullRowRankWitness basis) : FullRankLLLResult basis := by
  by_cases empty : rows = 0
  · subst rows
    exact
      { U := 1
        U_cert := MatrixInverseCertificate.one
        reducedBasis := basis
        equation := by simp
        reduced := emptyRowsReduced basis }
  · exact fullRankLLLPositive basis (Nat.one_le_iff_ne_zero.mpr empty) fullRank

/-- Total exact integer LLL for row-vector bases. -/
public opaque integerLLL {rows columns : Nat}
    (basis : Matrix (Fin rows) (Fin columns) Int) : LLLResult basis := by
  let decomposition := rowRankDecomposition basis
  let prefixBasis := rowPrefix decomposition.rank_le_rows decomposition.echelon
  let reduced := reduceIndependentPrefix prefixBasis decomposition.prefixFullRank
  let lifted := liftPrefixTransform decomposition.rank_le_rows reduced.U
  let result := extendPrefixWithZeros decomposition.rank_le_rows reduced.reducedBasis
  have liftedEquation : lifted * decomposition.echelon = result := by
    calc
      lifted * decomposition.echelon =
          extendPrefixWithZeros decomposition.rank_le_rows
            (reduced.U * rowPrefix decomposition.rank_le_rows decomposition.echelon) :=
        liftPrefixTransform_mul_of_zeroTail decomposition.rank_le_rows reduced.U
          decomposition.echelon decomposition.zeroTail
      _ = result := by rw [reduced.equation]
  exact
    { rank := decomposition.rank
      rank_le_rows := decomposition.rank_le_rows
      U := lifted * decomposition.transform
      U_cert :=
        (liftPrefixCertificate decomposition.rank_le_rows reduced.U_cert).mul
          decomposition.transformCert
      reducedBasis := result
      equation := by
        calc
          (lifted * decomposition.transform) * basis =
              lifted * (decomposition.transform * basis) := Matrix.mul_assoc ..
          _ = lifted * decomposition.echelon := by rw [decomposition.equation]
          _ = result := liftedEquation
      reducedPrefix := by
        simpa [result] using reduced.reduced
      zeroTail := extendPrefixWithZeros_zeroTail
        decomposition.rank_le_rows reduced.reducedBasis }

/-- Column-basis adapter obtained solely by transposing the total row result. -/
public opaque integerColumnLLL {rows columns : Nat}
    (basis : Matrix (Fin rows) (Fin columns) Int) : ColumnLLLResult basis := by
  let rowResult := integerLLL basis.transpose
  exact
    { rank := rowResult.rank
      rank_le_columns := rowResult.rank_le_rows
      V := rowResult.U.transpose
      V_cert := rowResult.U_cert.transpose
      reducedBasis := rowResult.reducedBasis.transpose
      equation := by
        have transposed := congrArg Matrix.transpose rowResult.equation
        simpa [Matrix.transpose_mul] using transposed
      reducedRows := by
        simpa using rowResult.reducedPrefix
      zeroColumnTail := by
        intro column afterRank
        have zero := rowResult.zeroTail column afterRank
        apply funext
        intro row
        exact congrFun zero row }

end NormalForms.Research.LLL
