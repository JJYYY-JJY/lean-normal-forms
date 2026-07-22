/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.Trace
public import NormalForms.Euclidean.Int
public import NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Hermite.Algorithm

/-!
# Semantic Target for Verified Kannan--Bachem HNF

The frozen constructive HNF kernel supplies the semantic target.  The adapter
below binds that strong result to a reversible trace as one explicitly opaque
certified block.  It proves the complete forward and inverse semantics now,
while making it impossible to reuse this adapter as the later primitive
operation-count witness.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite

/--
Instrumentation attached to an existing strong HNF result.  This is not a
second normal-form result type: `result` remains the frozen `HNFResultFin`.
-/
public structure ExecutionTrace {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (result : HNFResultFin A) where
  steps : RowTrace Int m
  accumulator_eq : steps.accumulator = result.U
  inverseAccumulator_eq : steps.inverseAccumulator = result.U_cert.inverse

namespace ExecutionTrace

/-- Replay reaches exactly the matrix stored by the strong HNF result. -/
public theorem replay_eq_result {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    {result : HNFResultFin A} (trace : ExecutionTrace A result) :
    trace.steps.replay A = result.H := by
  rw [RowTrace.replay_eq_accumulator_mul, trace.accumulator_eq, result.equation]

/-- The accumulated inverse takes the HNF matrix back to the input matrix. -/
public theorem inverse_mul_result {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    {result : HNFResultFin A} (trace : ExecutionTrace A result) :
    trace.steps.inverseAccumulator * result.H = A := by
  rw [trace.inverseAccumulator_eq, ← result.equation, ← Matrix.mul_assoc,
    result.U_cert.left_inv]
  simp

/-- Bind any strong result to one semantically valid, explicitly opaque step. -/
@[expose] public def ofResult {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (result : HNFResultFin A) : ExecutionTrace A result :=
  { steps := [ReversibleRowStep.certifiedBlock result.U_cert]
    accumulator_eq := by
      simp [RowTrace.accumulator, ReversibleRowStep.certifiedBlock,
        ReversibleRowStep.ofCertificate]
    inverseAccumulator_eq := by
      simp [RowTrace.inverseAccumulator, ReversibleRowStep.certifiedBlock,
        ReversibleRowStep.ofCertificate] }

@[simp] public theorem ofResult_certifiedBlocks {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (result : HNFResultFin A) :
    ((ofResult result).steps.operationCount).certifiedBlocks = 1 := by
  simp [ofResult, RowTrace.operationCount, OperationCount.singleton,
    OperationCount.add, ReversibleRowStep.certifiedBlock,
    ReversibleRowStep.ofCertificate]

public theorem ofResult_not_primitive {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (result : HNFResultFin A) :
    ¬ (ofResult result).steps.IsPrimitive := by
  simp [RowTrace.IsPrimitive, ofResult_certifiedBlocks]

end ExecutionTrace

/-- The strong integer HNF result used as the research line's semantic target. -/
@[expose] public def semanticReference {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : HNFResultFin A :=
  hermiteNormalFormFin A

/-- A semantic trace for the reference result, deliberately using one opaque block. -/
@[expose] public def semanticReferenceTrace {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    ExecutionTrace A (semanticReference A) :=
  ExecutionTrace.ofResult (semanticReference A)

public theorem semanticReference_equation {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (semanticReference A).U * A = (semanticReference A).H :=
  (semanticReference A).equation

public theorem semanticReference_isHermite {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    IsHermiteNormalFormFin (semanticReference A).H :=
  (semanticReference A).isHermite

public theorem semanticReference_inverse_equation {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (semanticReference A).U_cert.inverse * (semanticReference A).H = A := by
  rw [← (semanticReference A).equation, ← Matrix.mul_assoc,
    (semanticReference A).U_cert.left_inv]
  simp

public theorem semanticReference_trace_not_primitive {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :
    ¬ (semanticReferenceTrace A).steps.IsPrimitive :=
  ExecutionTrace.ofResult_not_primitive (semanticReference A)

end NormalForms.Research.KannanBachem.Hermite
