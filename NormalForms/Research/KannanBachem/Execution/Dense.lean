/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Charge
public import NormalForms.Research.KannanBachem.Smith.BitComplexity

/-!
# Costed Dense Products and Certificate Composition

Every matrix entry is constructed from sign-magnitude multiplication and
addition runs.  Strong-certificate composition obtains all four transform
matrices from four such executions.
-/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix BigOperators
open NormalForms.Matrix.Certificates
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Smith

/-- One scalar dot-product execution. -/
public structure DotProductExecution where
  value : SignMagnitude
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

/-- Checked location for one dense-product scalar term. -/
@[expose] public def matrixEntryLocation {n : Nat}
    (row column index : Fin n) : ArithmeticChargeLocation :=
  ArithmeticChargeLocation.ofIndices .scalar n
    [row.val, column.val, index.val] (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact row.isLt
      · exact column.isLt
      · exact index.isLt)

/-- Execute a list of dense-product scalar terms. -/
@[expose] public def matrixEntryLoop {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int)
    (row column : Fin n) :
    List (Fin n) → DotProductExecution
  | [] =>
      { value := 0
        charges := []
        trace_wellFormed := by
          simp [ArithmeticChargeListWellFormed] }
  | index :: tail =>
      let encodedLeft := SignMagnitude.ofInt (left row index)
      let encodedRight := SignMagnitude.ofInt (right index column)
      let multiplicationRun := mulWithCost encodedLeft encodedRight
      let rest := matrixEntryLoop left right row column tail
      let additionRun := addWithCost multiplicationRun.value rest.value
      let location := matrixEntryLocation row column index
      let multiplicationCharge :=
        KannanBachemArithmeticCharge.multiplicationOfRun
          location encodedLeft encodedRight multiplicationRun rfl
      let additionCharge :=
        KannanBachemArithmeticCharge.additionOfRun
          location multiplicationRun.value rest.value additionRun rfl
      { value := additionRun.value
        charges := [multiplicationCharge] ++ rest.charges ++ [additionCharge]
        trace_wellFormed := by
          apply (by
            simp only [ArithmeticChargeListWellFormed, List.forall_cons]
            exact
              ⟨KannanBachemArithmeticCharge.multiplicationOfRun_wellFormed
                  location encodedLeft encodedRight multiplicationRun rfl,
                by simp⟩ : ArithmeticChargeListWellFormed
                  [multiplicationCharge]).append
          apply rest.trace_wellFormed.append
          simp only [ArithmeticChargeListWellFormed, List.forall_cons]
          exact
            ⟨KannanBachemArithmeticCharge.additionOfRun_wellFormed
                location multiplicationRun.value rest.value additionRun rfl,
              by simp⟩ }

/-- Execute one dense matrix entry in index order. -/
@[expose] public def matrixEntryExecution {n : Nat}
  (left right : Matrix (Fin n) (Fin n) Int)
    (row column : Fin n) : DotProductExecution :=
  matrixEntryLoop left right row column (List.finRange n)

private theorem matrixEntryLoop_value
    {n : Nat} (left right : Matrix (Fin n) (Fin n) Int)
    (row column : Fin n) (indices : List (Fin n)) :
    (matrixEntryLoop left right row column indices).value.value =
      (indices.map fun index ↦ left row index * right index column).sum := by
  induction indices with
  | nil => simp [matrixEntryLoop]
  | cons index tail ih =>
      simp only [matrixEntryLoop, addWithCost_value, mulWithCost_value,
        SignMagnitude.value_ofInt, List.map_cons, List.sum_cons]
      rw [ih]

private theorem matrixEntryLoop_cost
    {n : Nat} (left right : Matrix (Fin n) (Fin n) Int)
    (row column : Fin n) (indices : List (Fin n)) :
    traceBitCost (matrixEntryLoop left right row column indices).charges =
      (Hermite.DivisionFreeDeterminant.dotWithCost indices
        (fun index ↦ SignMagnitude.ofInt (left row index))
        (fun index ↦ SignMagnitude.ofInt (right index column))).cost := by
  induction indices with
  | nil => simp [matrixEntryLoop, traceBitCost,
      Hermite.DivisionFreeDeterminant.dotWithCost]
  | cons index tail ih =>
      have restValue :
          (matrixEntryLoop left right row column tail).value =
            (Hermite.DivisionFreeDeterminant.dotWithCost tail
              (fun index ↦ SignMagnitude.ofInt (left row index))
              (fun index ↦
                SignMagnitude.ofInt (right index column))).value := by
        apply Hermite.DivisionFreeDeterminant.signMagnitude_value_injective
        rw [matrixEntryLoop_value,
          Hermite.DivisionFreeDeterminant.dotWithCost_value]
        simp only [SignMagnitude.value_ofInt]
      rw [matrixEntryLoop]
      dsimp only
      rw [traceBitCost_append, traceBitCost_append, ih]
      simp only [traceBitCost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, KannanBachemArithmeticCharge.multiplicationOfRun,
        KannanBachemArithmeticCharge.additionOfRun,
        KannanBachemArithmeticCharge.bitCost, add_zero]
      rw [restValue]
      simp [Hermite.DivisionFreeDeterminant.dotWithCost]

private theorem finRange_sum_eq_univ {n : Nat} (values : Fin n → Int) :
    (List.map values (List.finRange n)).sum = ∑ index, values index := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map,
        NormalForms.Matrix.Constructive.sum_univ_succ]
      rw [ih]
      simp [Function.comp_apply]

public theorem matrixEntryExecution_value {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int)
    (row column : Fin n) :
    (matrixEntryExecution left right row column).value.value =
      (left * right) row column := by
  rw [matrixEntryExecution, matrixEntryLoop_value]
  rw [Matrix.mul_apply, finRange_sum_eq_univ]

public theorem matrixEntryExecution_cost_eq {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int)
    (row column : Fin n) :
    traceBitCost (matrixEntryExecution left right row column).charges =
      (matrixEntryWithCost left right row column).cost := by
  exact matrixEntryLoop_cost left right row column (List.finRange n)

/-- Runtime data for one complete dense product. -/
public structure MatrixProductExecution {n : Nat} where
  entries : Matrix (Fin n) (Fin n) DotProductExecution

namespace MatrixProductExecution

@[expose] public def value {n : Nat}
    (execution : MatrixProductExecution (n := n)) :
    Matrix (Fin n) (Fin n) Int :=
  fun row column => (execution.entries row column).value.value

@[expose] public def charges {n : Nat}
    (execution : MatrixProductExecution (n := n)) :
    List KannanBachemArithmeticCharge :=
  (List.finRange n).flatMap fun row ↦
    (List.finRange n).flatMap fun column ↦
      (execution.entries row column).charges

public theorem trace_wellFormed {n : Nat}
    (execution : MatrixProductExecution (n := n)) :
    ArithmeticChargeListWellFormed execution.charges := by
  rw [ArithmeticChargeListWellFormed, List.forall_iff_forall_mem]
  intro charge member
  rw [charges, List.mem_flatMap] at member
  obtain ⟨row, _rowMember, member⟩ := member
  rw [List.mem_flatMap] at member
  obtain ⟨column, _columnMember, member⟩ := member
  exact (List.forall_iff_forall_mem.mp
    (execution.entries row column).trace_wellFormed) charge member

end MatrixProductExecution

/-- Execute every entry of one dense square matrix product. -/
@[expose] public def matrixProductExecution {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) :
    MatrixProductExecution (n := n) :=
  { entries := fun row column =>
      matrixEntryExecution left right row column }

public theorem matrixProductExecution_value {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) :
    (matrixProductExecution left right).value = left * right := by
  ext row column
  exact matrixEntryExecution_value left right row column

private theorem traceBitCost_flatMap {α : Type*} (values : List α)
    (f : α → List KannanBachemArithmeticCharge) :
    traceBitCost (values.flatMap f) =
      (values.map fun value ↦ traceBitCost (f value)).sum := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [traceBitCost_append, ih]

private theorem finRange_nat_sum_eq_univ {n : Nat} (values : Fin n → Nat) :
    (List.map values (List.finRange n)).sum = ∑ index, values index := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map,
        NormalForms.Matrix.Constructive.sum_univ_succ]
      rw [ih]
      simp [Function.comp_apply]

public theorem matrixProductExecution_cost_eq {n : Nat}
    (left right : Matrix (Fin n) (Fin n) Int) :
    traceBitCost (matrixProductExecution left right).charges =
      matrixMultiplicationBitOperationCost left right := by
  rw [MatrixProductExecution.charges]
  simp only [matrixProductExecution]
  rw [traceBitCost_flatMap]
  simp_rw [traceBitCost_flatMap, matrixEntryExecution_cost_eq]
  rw [matrixMultiplicationBitOperationCost]
  rw [finRange_nat_sum_eq_univ]
  apply Finset.sum_congr rfl
  intro row _member
  exact finRange_nat_sum_eq_univ _

/-- Value-producing two-sided certificate execution with one flat leaf trace. -/
public structure CertificateExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) where
  value : TwoSidedCertificate A
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

public theorem twoSidedCertificate_ext_data {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (left right : TwoSidedCertificate A)
    (u_eq : left.U = right.U)
    (uinv_eq : left.U_cert.inverse = right.U_cert.inverse)
    (result_eq : left.result = right.result)
    (v_eq : left.V = right.V)
    (vinv_eq : left.V_cert.inverse = right.V_cert.inverse) :
    left = right := by
  cases left with
  | mk leftU leftUCert leftResult leftV leftVCert leftEquation =>
      cases right with
      | mk rightU rightUCert rightResult rightV rightVCert rightEquation =>
          dsimp only at u_eq uinv_eq result_eq v_eq vinv_eq
          subst rightU
          subst rightResult
          subst rightV
          have ucert_eq : leftUCert = rightUCert := by
            cases leftUCert
            cases rightUCert
            simp_all
          have vcert_eq : leftVCert = rightVCert := by
            cases leftVCert
            cases rightVCert
            simp_all
          subst rightUCert
          subst rightVCert
          rfl

/-- Treat an already value-producing certificate as a charge-free execution. -/
@[expose] public def CertificateExecution.pure {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (value : TwoSidedCertificate A) : CertificateExecution A :=
  { value, charges := []
    trace_wellFormed := by simp [ArithmeticChargeListWellFormed] }

/--
Compose two executions using exactly four dense products for the two forward
and two inverse transforms.
-/
@[expose] public def composeExecution {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (first : CertificateExecution A)
    (second : CertificateExecution first.value.result) :
    CertificateExecution A := by
  let leftForward := matrixProductExecution second.value.U first.value.U
  let leftInverse := matrixProductExecution first.value.U_cert.inverse
    second.value.U_cert.inverse
  let rightForward := matrixProductExecution first.value.V second.value.V
  let rightInverse := matrixProductExecution second.value.V_cert.inverse
    first.value.V_cert.inverse
  have leftForwardValue :
      leftForward.value = second.value.U * first.value.U :=
    matrixProductExecution_value _ _
  have leftInverseValue :
      leftInverse.value =
        first.value.U_cert.inverse * second.value.U_cert.inverse :=
    matrixProductExecution_value _ _
  have rightForwardValue :
      rightForward.value = first.value.V * second.value.V :=
    matrixProductExecution_value _ _
  have rightInverseValue :
      rightInverse.value =
        second.value.V_cert.inverse * first.value.V_cert.inverse :=
    matrixProductExecution_value _ _
  let leftCertificate : MatrixInverseCertificate leftForward.value :=
    { inverse := leftInverse.value
      left_inv := by
        rw [leftForwardValue, leftInverseValue]
        exact (second.value.U_cert.mul first.value.U_cert).left_inv
      right_inv := by
        rw [leftForwardValue, leftInverseValue]
        exact (second.value.U_cert.mul first.value.U_cert).right_inv }
  let rightCertificate : MatrixInverseCertificate rightForward.value :=
    { inverse := rightInverse.value
      left_inv := by
        rw [rightForwardValue, rightInverseValue]
        exact (first.value.V_cert.mul second.value.V_cert).left_inv
      right_inv := by
        rw [rightForwardValue, rightInverseValue]
        exact (first.value.V_cert.mul second.value.V_cert).right_inv }
  let value : TwoSidedCertificate A :=
    { U := leftForward.value
      U_cert := leftCertificate
      result := second.value.result
      V := rightForward.value
      V_cert := rightCertificate
      equation := by
        rw [leftForwardValue, rightForwardValue]
        calc
          (second.value.U * first.value.U) * A *
                (first.value.V * second.value.V) =
              second.value.U *
                (first.value.U * A * first.value.V) * second.value.V := by
                  simp only [Matrix.mul_assoc]
          _ = second.value.U * first.value.result * second.value.V := by
            rw [first.value.equation]
          _ = second.value.result := second.value.equation }
  let charges := first.charges ++ (second.charges ++
    (leftForward.charges ++ (leftInverse.charges ++
    (rightForward.charges ++ rightInverse.charges))))
  have chargesWellFormed : ArithmeticChargeListWellFormed charges := by
    apply first.trace_wellFormed.append
    apply second.trace_wellFormed.append
    apply leftForward.trace_wellFormed.append
    apply leftInverse.trace_wellFormed.append
    exact rightForward.trace_wellFormed.append
      rightInverse.trace_wellFormed
  exact
    { value
      charges
      trace_wellFormed := chargesWellFormed }

public theorem composeExecution_value {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (first : CertificateExecution A)
    (second : CertificateExecution first.value.result) :
    (composeExecution first second).value =
      compose first.value second.value := by
  apply twoSidedCertificate_ext_data
  · change (matrixProductExecution second.value.U first.value.U).value =
      second.value.U * first.value.U
    exact matrixProductExecution_value _ _
  · change
      (matrixProductExecution first.value.U_cert.inverse
          second.value.U_cert.inverse).value =
        first.value.U_cert.inverse * second.value.U_cert.inverse
    exact matrixProductExecution_value _ _
  · rfl
  · change (matrixProductExecution first.value.V second.value.V).value =
      first.value.V * second.value.V
    exact matrixProductExecution_value _ _
  · change
      (matrixProductExecution second.value.V_cert.inverse
          first.value.V_cert.inverse).value =
        second.value.V_cert.inverse * first.value.V_cert.inverse
    exact matrixProductExecution_value _ _

public theorem composeExecution_cost_eq {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (first : CertificateExecution A)
    (second : CertificateExecution first.value.result) :
    traceBitCost (composeExecution first second).charges =
      traceBitCost first.charges + traceBitCost second.charges +
        certificateCompositionBitOperationCost first.value second.value := by
  simp [composeExecution, traceBitCost_append,
    matrixProductExecution_cost_eq,
    certificateCompositionBitOperationCost]
  omega

/-- Program-structure count of dense products in one composition. -/
@[expose] public def composeExecutionDenseProductCount : Nat := 4

public theorem composeExecution_denseProducts_eq_four :
    composeExecutionDenseProductCount = 4 :=
  rfl

end NormalForms.Research.KannanBachem
