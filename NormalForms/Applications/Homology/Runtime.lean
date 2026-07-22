/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology.Decomposition
import all NormalForms.Matrix.Smith.Algorithm
import all NormalForms.Matrix.Smith.Defs

/-!
# Executable Integer Homology Projection

The theorem-facing quotient equivalences are necessarily noncomputable. This
module keeps the matrix path executable: it reads the nonzero Smith prefix,
extracts the kernel-tail boundary matrix, runs the second strong Smith
calculation, and returns a small deterministic summary.
-/

public section

namespace NormalForms.Applications.Homology

open NormalForms.Matrix.Smith

namespace IntChainComplex

private def executableSmithFactors
    {m n : Nat} {A : Matrix (Fin m) (Fin n) Int}
    (result : SNFResultFin A) : List Int :=
  NormalForms.Matrix.Smith.Internal.invariantFactors result.S

/-- Executable rank of the outgoing differential. -/
public def runtimeOutgoingRank
    (complex : IntChainComplex) (n : Nat) : Nat :=
  executableSmithFactors (complex.outgoingSmithResult n) |>.length

private theorem runtimeOutgoingRank_eq_outgoingSmithRankImpl
    (complex : IntChainComplex) (n : Nat) :
    complex.runtimeOutgoingRank n = complex.outgoingSmithRank n :=
  rfl

/--
The executable prefix length is exactly the intrinsic outgoing Smith rank.
-/
public theorem runtimeOutgoingRank_eq_outgoingSmithRank
    (complex : IntChainComplex) (n : Nat) :
    complex.runtimeOutgoingRank n = complex.outgoingSmithRank n :=
  runtimeOutgoingRank_eq_outgoingSmithRankImpl complex n

private theorem runtimeOutgoingRank_le_chainRankImpl
    (complex : IntChainComplex) (n : Nat) :
    complex.runtimeOutgoingRank n ≤ complex.rank n := by
  rw [complex.runtimeOutgoingRank_eq_outgoingSmithRank n]
  exact complex.outgoingSmithRank_le_chainRank n

public theorem runtimeOutgoingRank_le_chainRank
    (complex : IntChainComplex) (n : Nat) :
    complex.runtimeOutgoingRank n ≤ complex.rank n :=
  runtimeOutgoingRank_le_chainRankImpl complex n

/-- Executable rank of the outgoing kernel. -/
public def runtimeKernelRank
    (complex : IntChainComplex) (n : Nat) : Nat :=
  complex.rank n - complex.runtimeOutgoingRank n

public theorem runtimeKernelRank_eq_kernelRank
    (complex : IntChainComplex) (n : Nat) :
    complex.runtimeKernelRank n = complex.kernelRank n := by
  rw [runtimeKernelRank, kernelRank,
    complex.runtimeOutgoingRank_eq_outgoingSmithRank]

/-- Index equivalence connecting executable and theorem-facing kernel ranks. -/
public noncomputable def runtimeKernelIndexEquiv
    (complex : IntChainComplex) (n : Nat) :
    Fin (complex.runtimeKernelRank n) ≃ Fin (complex.kernelRank n) :=
  finCongr (complex.runtimeKernelRank_eq_kernelRank n)

/-- Kernel-tail index used by the executable matrix path. -/
public def runtimeKernelColumnIndex
    (complex : IntChainComplex) (n : Nat)
    (i : Fin (complex.runtimeKernelRank n)) :
    Fin (complex.rank n) :=
  ⟨complex.runtimeOutgoingRank n + i.1, by
    have hi := i.is_lt
    have hr := complex.runtimeOutgoingRank_le_chainRank n
    simp only [runtimeKernelRank] at hi
    omega⟩

/-- Executable incoming boundary matrix in the outgoing kernel basis. -/
public def runtimeKernelCoordinateMatrix
    (complex : IntChainComplex) (n : Nat) :
    Matrix
      (Fin (complex.runtimeKernelRank n))
      (Fin (complex.rank (n + 1))) Int :=
  fun i j =>
    complex.incomingSmithCoordinates n
      (complex.runtimeKernelColumnIndex n i) j

/--
The executable restricted boundary is exactly the theorem-facing matrix after
transport along the proved kernel-rank equality.
-/
public theorem runtimeKernelCoordinateMatrix_reindex
    (complex : IntChainComplex) (n : Nat) :
    Matrix.reindex
        (complex.runtimeKernelIndexEquiv n)
        (Equiv.refl (Fin (complex.rank (n + 1))))
        (complex.runtimeKernelCoordinateMatrix n) =
      complex.kernelCoordinateMatrix n := by
  ext i j
  change
    complex.incomingSmithCoordinates n
        (complex.runtimeKernelColumnIndex n
          ((complex.runtimeKernelIndexEquiv n).symm i)) j =
      complex.incomingSmithCoordinates n
        (complex.kernelColumnIndex n i) j
  congr 1

/--
The second strong Smith result on the executable restricted boundary matrix.
-/
public def runtimeHomologySmithResult
    (complex : IntChainComplex) (n : Nat) :
    SNFResultFin (complex.runtimeKernelCoordinateMatrix n) :=
  smithNormalFormFin (complex.runtimeKernelCoordinateMatrix n)

/-- Complete nonzero homology presentation factors, including units. -/
public def runtimeHomologyInvariantFactors
    (complex : IntChainComplex) (n : Nat) : List Nat :=
  (executableSmithFactors (complex.runtimeHomologySmithResult n)).map Int.natAbs

private theorem runtimeHomologyInvariantFactors_eq_strongImpl
    (complex : IntChainComplex) (n : Nat) :
    complex.runtimeHomologyInvariantFactors n =
      (smithInvariantFactorsFin
        (complex.runtimeHomologySmithResult n).S).map Int.natAbs :=
  rfl

/--
The executable factor list is read directly from the second strong Smith
result, rather than from an unchecked external computation.
-/
public theorem runtimeHomologyInvariantFactors_eq_strong
    (complex : IntChainComplex) (n : Nat) :
    complex.runtimeHomologyInvariantFactors n =
      (smithInvariantFactorsFin
        (complex.runtimeHomologySmithResult n).S).map Int.natAbs :=
  runtimeHomologyInvariantFactors_eq_strongImpl complex n

/-- Human-facing nontrivial torsion factors. -/
public def runtimeHomologyTorsionFactors
    (complex : IntChainComplex) (n : Nat) : List Nat :=
  (complex.runtimeHomologyInvariantFactors n).filter (fun factor => 1 < factor)

/-- Executable free rank of degree-`n` homology. -/
public def runtimeBettiNumber
    (complex : IntChainComplex) (n : Nat) : Nat :=
  complex.runtimeKernelRank n -
    (complex.runtimeHomologyInvariantFactors n).length

/-- Small serializable result of the trusted-by-rechecking runtime path. -/
public structure RuntimeHomologySummary where
  degree : Nat
  chainRank : Nat
  outgoingRank : Nat
  kernelRank : Nat
  invariantFactors : List Nat
  torsionFactors : List Nat
  bettiNumber : Nat
  deriving Repr, DecidableEq

/-- Execute both strong Smith calculations and project their canonical data. -/
public def runtimeHomologySummary
    (complex : IntChainComplex) (n : Nat) :
    RuntimeHomologySummary :=
  { degree := n
    chainRank := complex.rank n
    outgoingRank := complex.runtimeOutgoingRank n
    kernelRank := complex.runtimeKernelRank n
    invariantFactors := complex.runtimeHomologyInvariantFactors n
    torsionFactors := complex.runtimeHomologyTorsionFactors n
    bettiNumber := complex.runtimeBettiNumber n }

end IntChainComplex

end NormalForms.Applications.Homology
