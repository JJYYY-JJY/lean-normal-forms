/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Semantic
import all NormalForms.Research.ModularHNF.Semantic

/-!
# Strong full-column-rank modular HNF result

The DKT kernel computes the canonical matrix.  The stable strong-result seam
also requires a full-size left transform and its explicit inverse.  Until the
general rank-profile layer supplies a primitive transform trace, those fields
are recovered from the already certified canonical reference; the `H` field
itself remains definitionally the modular candidate.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms.Matrix.Hermite

/--
Certified full-column-rank modular HNF.  Its matrix field is the raw DKT
candidate; its reversible transform is the canonical certificate for the same
matrix, transported across the proved candidate equality.
-/
@[expose] public def modularHNFFullRank {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) : HNFResultFin A := by
  let run := runWithDeterminantWitness A fullRank witness
  let reference := hermiteNormalFormFin A
  have candidateEq : run.candidate = reference.H := by
    simpa [run, reference] using
      (runWithDeterminantWitness_candidate_eq_reference A fullRank witness)
  exact
    { U := reference.U
      U_cert := reference.U_cert
      H := run.candidate
      equation := reference.equation.trans candidateEq.symm
      isHermite := by
        simpa [run, runWithDeterminantWitness] using
          (runRaw_isHermite A fullRank.columns_le_rows witness.modulus
            witness.positive) }

@[simp] public theorem modularHNFFullRank_H {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) :
    (modularHNFFullRank A fullRank witness).H =
      (runWithDeterminantWitness A fullRank witness).candidate := by
  rfl

public theorem modularHNFFullRank_eq_reference {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) :
    (modularHNFFullRank A fullRank witness).H =
      (hermiteNormalFormFin A).H :=
  runWithDeterminantWitness_candidate_eq_reference A fullRank witness

public theorem modularHNFFullRank_inverse_equation {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (witness : DeterminantModulusWitness A fullRank) :
    (modularHNFFullRank A fullRank witness).U_cert.inverse *
        (modularHNFFullRank A fullRank witness).H = A := by
  let result := modularHNFFullRank A fullRank witness
  rw [← result.equation, ← _root_.Matrix.mul_assoc,
    result.U_cert.left_inv]
  simp

end NormalForms.Research.ModularHNF
