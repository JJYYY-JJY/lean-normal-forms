/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalTypes
public import NormalForms.Matrix.Smith.Defs
import all NormalForms.Research.KannanBachem.Hermite.PrincipalInternal
import all NormalForms.Research.KannanBachem.Hermite.BoundedXGCD

/-!
# Size-controlled one-column Hermite reduction

Step 4 of the Kannan--Bachem Smith schedule only needs to clear one column.
This module performs that reduction with the bounded-XGCD primitive used by the
principal-minor HNF kernel.  It accumulates explicit forward and inverse
matrices and exposes the result through the existing strong `HNFResultFin`.
-/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem.Hermite

namespace BoundedColumn

open Principal

def firstColumn {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    _root_.Matrix (Fin (n + 1)) (Fin 1) Int :=
  fun row _ => A row 0

def pairAtFirstColumn {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (target : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target)
    (state : Transform A) : Transform A :=
  let forward := boundedPairBezoutMatrix 0 target
    (state.B 0 0) (state.B target 0)
  let certificate := boundedPairBezoutMatrixInverseCertificate 0 target hne
    (state.B 0 0) (state.B target 0)
  state.trans <| Transform.ofPrimitive
    forward certificate (forward * state.B) rfl .bezoutPair (by decide)

theorem pairAtFirstColumn_pivot_apply {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (target : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target)
    (state : Transform A) (column : Fin (n + 1)) :
    (pairAtFirstColumn target hne state).B 0 column =
      boundedBezoutReductionMatrix (state.B 0 0) (state.B target 0) 0 0 *
          state.B 0 column +
        boundedBezoutReductionMatrix (state.B 0 0) (state.B target 0) 0 1 *
          state.B target column := by
  exact twoRowLiftMatrix_mul_apply_pivot 0 target hne
    (boundedBezoutReductionMatrix (state.B 0 0) (state.B target 0))
    state.B column

theorem pairAtFirstColumn_target_apply {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (target : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target)
    (state : Transform A) (column : Fin (n + 1)) :
    (pairAtFirstColumn target hne state).B target column =
      boundedBezoutReductionMatrix (state.B 0 0) (state.B target 0) 1 0 *
          state.B 0 column +
        boundedBezoutReductionMatrix (state.B 0 0) (state.B target 0) 1 1 *
          state.B target column := by
  exact twoRowLiftMatrix_mul_apply_target 0 target
    (boundedBezoutReductionMatrix (state.B 0 0) (state.B target 0))
    state.B column

theorem pairAtFirstColumn_other_apply {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (target row : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target)
    (hzero : row ≠ 0) (htarget : row ≠ target)
    (state : Transform A) (column : Fin (n + 1)) :
    (pairAtFirstColumn target hne state).B row column = state.B row column := by
  exact twoRowLiftMatrix_mul_apply_other 0 target row hzero htarget
    (boundedBezoutReductionMatrix (state.B 0 0) (state.B target 0))
    state.B column

theorem pairAtFirstColumn_pivot {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (target : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target)
    (state : Transform A) :
    (pairAtFirstColumn target hne state).B 0 0 =
      (boundedIntXGCD (state.B 0 0) (state.B target 0)).gcd := by
  rw [pairAtFirstColumn_pivot_apply]
  have entry := congrFun
    (boundedBezoutReductionMatrix_mulVec
      (state.B 0 0) (state.B target 0)) 0
  simpa [_root_.Matrix.mulVec, dotProduct,
    NormalForms.Matrix.Constructive.sum_univ_two] using entry

theorem pairAtFirstColumn_target_zero {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (target : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target)
    (state : Transform A) :
    (pairAtFirstColumn target hne state).B target 0 = 0 := by
  rw [pairAtFirstColumn_target_apply]
  have entry := congrFun
    (boundedBezoutReductionMatrix_mulVec
      (state.B 0 0) (state.B target 0)) 1
  simpa [_root_.Matrix.mulVec, dotProduct,
    NormalForms.Matrix.Constructive.sum_univ_two] using entry

def loop {n : Nat} {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → k ≤ n → Transform A → Transform A
  | 0, _hk, state => state
  | k + 1, hk, state =>
      let previous := loop k (by omega) state
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      pairAtFirstColumn target (by simp [target]) previous

theorem loop_steps_length {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      (loop k hk state).steps.length = state.steps.length + k
  | 0, _hk, _state => by rfl
  | k + 1, hk, state => by
      rw [loop]
      simp [pairAtFirstColumn, Transform.trans, Transform.ofPrimitive,
        loop_steps_length k (by omega) state]
      omega

theorem loop_prefix_zero {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      ∀ row : Fin k,
        (loop k hk state).B (Fin.castLE hk row).succ 0 = 0
  | 0, _hk, _state, row => Fin.elim0 row
  | k + 1, hk, state, row => by
      rw [loop]
      let previous := loop k (by omega) state
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      refine Fin.lastCases ?_ (fun earlier => ?_) row
      · change (pairAtFirstColumn target (by simp [target]) previous).B target 0 = 0
        exact pairAtFirstColumn_target_zero target (by simp [target]) previous
      · have rowNeZero : (Fin.castLE hk earlier.castSucc).succ ≠
            (0 : Fin (n + 1)) := by simp
        have rowNeTarget : (Fin.castLE hk earlier.castSucc).succ ≠ target := by
          intro equality
          have valueEquality := congrArg Fin.val equality
          simp [target] at valueEquality
          omega
        rw [pairAtFirstColumn_other_apply target
          (Fin.castLE hk earlier.castSucc).succ (by simp [target])
          rowNeZero rowNeTarget previous 0]
        simpa using loop_prefix_zero k (by omega) state earlier

def compute {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Transform A :=
  let reduced := loop n le_rfl (Transform.refl A)
  reduced.trans <| Transform.unitScale reduced.B 0
    (ComputableEuclideanOps.normUnitUnit (reduced.B 0 0))

theorem compute_steps_length {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (compute A).steps.length = n + 1 := by
  simp [compute, Transform.trans, Transform.unitScale, Transform.ofPrimitive,
    loop_steps_length, Transform.refl]

theorem compute_below_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (row : Fin n) : (compute A).B row.succ 0 = 0 := by
  let reduced := loop n le_rfl (Transform.refl A)
  have reducedZero := loop_prefix_zero n le_rfl (Transform.refl A) row
  simpa [compute, reduced, Transform.trans, Transform.unitScale,
    Transform.ofPrimitive, applyRowOperation] using reducedZero

theorem compute_pivot_normalized {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (compute A).B 0 0 = _root_.normalize ((compute A).B 0 0) := by
  simp [compute, Transform.trans, Transform.unitScale, Transform.ofPrimitive,
    applyRowOperation, normalize_apply, mul_comm]

def arithmeticLoop {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → k ≤ n → Transform A → List PrincipalArithmeticEvent
  | 0, _hk, _state => []
  | k + 1, hk, state =>
      let previous := loop k (by omega) state
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      arithmeticLoop k (by omega) state ++
        [.xgcd 0 target.val (previous.B 0 0) (previous.B target 0)]

def arithmeticEvents {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    List PrincipalArithmeticEvent :=
  let reduced := loop n le_rfl (Transform.refl A)
  arithmeticLoop n le_rfl (Transform.refl A) ++
    [.normalize 0 (reduced.B 0 0)]

theorem arithmeticLoop_valid {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      (arithmeticLoop k hk state).Forall
        (PrincipalArithmeticEvent.Valid (n + 1))
  | 0, _hk, _state => by simp [arithmeticLoop]
  | k + 1, hk, state => by
      rw [arithmeticLoop, List.forall_append]
      constructor
      · exact arithmeticLoop_valid k (by omega) state
      · rw [List.forall_cons]
        constructor
        · change 0 < k + 1 ∧ k + 1 < n + 1
          omega
        · simp

theorem arithmeticLoop_length {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      (arithmeticLoop k hk state).length = k
  | 0, _hk, _state => rfl
  | k + 1, hk, state => by
      rw [arithmeticLoop, List.length_append,
        arithmeticLoop_length k (by omega) state]
      simp

theorem arithmeticEvents_length {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (arithmeticEvents A).length = n + 1 := by
  simp [arithmeticEvents, arithmeticLoop_length]

theorem compute_firstColumn_isHermite {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    IsHermiteNormalFormFin (firstColumn (compute A).B) := by
  by_cases hpivot : (compute A).B 0 0 = 0
  · apply IsHermiteNormalFormFin.zeroCol
    · intro row
      cases row using Fin.cases with
      | zero => simpa [firstColumn] using hpivot
      | succ row => simpa [firstColumn] using compute_below_zero A row
    · exact IsHermiteNormalFormFin.emptyCols _
  · apply IsHermiteNormalFormFin.pivot
    · simpa [firstColumn] using hpivot
    · simpa [firstColumn] using compute_pivot_normalized A
    · intro row
      simpa [firstColumn] using compute_below_zero A row
    · exact IsHermiteNormalFormFin.emptyCols _
    · intro row
      simp [firstNonzero?]

/-- Primitive row trace executed by the size-controlled one-column reducer. -/
public def _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnTrace
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : RowTrace Int (n + 1) :=
  (compute A).steps

/-- Arithmetic operands consumed by the bounded one-column reducer. -/
public def _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnArithmeticEvents
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    List PrincipalArithmeticEvent :=
  arithmeticEvents A

public theorem
    _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnArithmeticEvents_valid
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnArithmeticEvents A).Forall
      (PrincipalArithmeticEvent.Valid (n + 1)) := by
  let reduced := loop n le_rfl (Transform.refl A)
  rw [boundedColumnArithmeticEvents, arithmeticEvents, List.forall_append]
  constructor
  · exact arithmeticLoop_valid n le_rfl (Transform.refl A)
  · rw [List.forall_cons]
    constructor
    · change (0 : Nat) < n + 1
      omega
    · simp

@[simp] public theorem _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnTrace_length
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnTrace A).length = n + 1 :=
  compute_steps_length A

@[simp] public theorem
    _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnArithmeticEvents_length
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnArithmeticEvents A).length = n + 1 :=
  arithmeticEvents_length A

/-- Strong one-column HNF result with explicit bounded-XGCD inverse data. -/
public def _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnHermiteNormalForm
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    HNFResultFin (fun row (_ : Fin 1) => A row 0) :=
  let result := compute A
  { U := result.U
    U_cert := result.U_cert
    H := fun row _ => result.B row 0
    equation := by
      ext row column
      fin_cases column
      simpa [firstColumn, _root_.Matrix.mul_apply] using
        congrFun (congrFun result.equation row) 0
    isHermite := compute_firstColumn_isHermite A }

public theorem
    _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnTrace_accumulator_eq
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnTrace A).accumulator =
      (boundedColumnHermiteNormalForm A).U :=
  (compute A).accumulator_eq

public theorem
    _root_.NormalForms.Research.KannanBachem.Smith.boundedColumnTrace_inverseAccumulator_eq
    {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnTrace A).inverseAccumulator =
      (boundedColumnHermiteNormalForm A).U_cert.inverse :=
  (compute A).inverseAccumulator_eq

end BoundedColumn

end NormalForms.Research.KannanBachem.Smith
