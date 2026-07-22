/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Predicate
public import NormalForms.Matrix.Certificates

/-!
# Strong LLL result contracts

The full-rank kernel and the total wrapper share the core explicit-inverse
certificate.  The total result identifies a reduced nonzero row prefix and a
literal zero tail.  Column-basis users receive only the transposed adapter.
-/

@[expose] public section

namespace NormalForms.Research.LLL

open scoped Matrix
open NormalForms.Matrix.Certificates

/-- Proof-only full-row-rank input contract for the total LLL kernel. -/
public structure FullRowRankWitness {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Prop where
  independent : (toDense basis).independent

/-- Restrict the first `rank` rows of a matrix. -/
public def rowPrefix {m n rank : Nat} (rank_le : rank <= m)
    (basis : Matrix (Fin m) (Fin n) Int) : Matrix (Fin rank) (Fin n) Int :=
  fun row column => basis (Fin.castLE rank_le row) column

/-- Strong result returned by the linearly independent row-basis kernel. -/
public structure FullRankLLLResult {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) where
  U : Matrix (Fin m) (Fin m) Int
  U_cert : MatrixInverseCertificate U
  reducedBasis : Matrix (Fin m) (Fin n) Int
  equation : U * basis = reducedBasis
  reduced : IsLLLReduced reducedBasis

/-- Total row-basis result, including dependent and zero-row inputs. -/
public structure LLLResult {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) where
  rank : Nat
  rank_le_rows : rank <= m
  U : Matrix (Fin m) (Fin m) Int
  U_cert : MatrixInverseCertificate U
  reducedBasis : Matrix (Fin m) (Fin n) Int
  equation : U * basis = reducedBasis
  reducedPrefix : IsLLLReduced (rowPrefix rank_le_rows reducedBasis)
  zeroTail : ∀ row : Fin m, rank <= row.1 -> reducedBasis row = 0

/-- Result of applying the row convention to a transposed column basis. -/
public structure ColumnLLLResult {n m : Nat}
    (basis : Matrix (Fin n) (Fin m) Int) where
  rank : Nat
  rank_le_columns : rank <= m
  V : Matrix (Fin m) (Fin m) Int
  V_cert : MatrixInverseCertificate V
  reducedBasis : Matrix (Fin n) (Fin m) Int
  equation : basis * V = reducedBasis
  reducedRows : IsLLLReduced
    (rowPrefix rank_le_columns reducedBasis.transpose)
  zeroColumnTail : ∀ column : Fin m, rank <= column.1 ->
    (fun row => reducedBasis row column) = 0

/-- Observable operation telemetry for one bounded LLL run. -/
public structure LLLOperationCount where
  sizeReductions : Nat
  swaps : Nat
  gramSchmidtRefreshes : Nat
  deriving DecidableEq, Repr, Nonempty

namespace LLLOperationCount

public def total (count : LLLOperationCount) : Nat :=
  count.sizeReductions + count.swaps + count.gramSchmidtRefreshes

end LLLOperationCount

/-- Public status report for a bounded diagnostic run. -/
public structure FuelledLLLRun {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) where
  complete : Bool
  iterations : Nat
  operations : LLLOperationCount
  candidate : Matrix (Fin m) (Fin n) Int
  certified : Option (FullRankLLLResult basis)
  deriving Nonempty

end NormalForms.Research.LLL
