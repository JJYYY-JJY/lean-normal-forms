/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Stabilization
public import NormalForms.Research.KannanBachem.Smith.Recursive
import all NormalForms.Matrix.Smith.Uniqueness

/-! # Single Instrumented Smith Recursion -/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Zero-cost runtime branch markers for benchmark diagnostics. -/
public structure SmithControlTrace where
  passes : Nat
  injections : Nat

/-- Runtime result and flat arithmetic trace of the outer dimension recursion. -/
public structure SmithExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) where
  value : SNFResultFin A
  charges : List KannanBachemArithmeticCharge
  controlTrace : SmithControlTrace
  trace_wellFormed : ArithmeticChargeListWellFormed charges
  chargeOwnership : ∀ charge ∈ charges, charge.WellFormed

private theorem snfResultFin_ext_data {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (left right : SNFResultFin A)
    (u_eq : left.U = right.U)
    (uinv_eq : left.U_cert.inverse = right.U_cert.inverse)
    (s_eq : left.S = right.S)
    (v_eq : left.V = right.V)
    (vinv_eq : left.V_cert.inverse = right.V_cert.inverse) :
    left = right := by
  cases left with
  | mk leftU leftUCert leftS leftV leftVCert leftEquation leftSmith =>
      cases right with
      | mk rightU rightUCert rightS rightV rightVCert rightEquation rightSmith =>
          dsimp only at u_eq uinv_eq s_eq v_eq vinv_eq
          subst rightU
          subst rightS
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

/-- Assemble an executed stable pivot with an executed lower-right result. -/
@[expose] public def assembleExecution {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (stabilized : StabilizationExecution A)
    (lower : SmithExecution
      (lowerRight stabilized.certificate.value.result)) :
    SmithExecution A := by
  let lowerCertificateValue : TwoSidedCertificate
      (lowerRight stabilized.certificate.value.result) :=
    { U := lower.value.U
      U_cert := lower.value.U_cert
      result := lower.value.S
      V := lower.value.V
      V_cert := lower.value.V_cert
      equation := lower.value.equation }
  let liftedValue := liftLowerCertificate
    stabilized.certificate.value.result stabilized.stable lowerCertificateValue
  let lifted : CertificateExecution stabilized.certificate.value.result :=
    { value := liftedValue
      charges := lower.charges
      trace_wellFormed := lower.trace_wellFormed
      chargeOwnership := lower.chargeOwnership }
  let final := composeExecution stabilized.certificate lifted
  let value : SNFResultFin A :=
    { U := final.value.U
      U_cert := final.value.U_cert
      S := final.value.result
      V := final.value.V
      V_cert := final.value.V_cert
      equation := final.value.equation
      isSmith := by
        change IsSmithNormalFormFin
          (adjoinPivot
            (stabilized.certificate.value.result 0 0) lower.value.S)
        refine IsSmithNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_ ?_
        · exact stabilized.stable.pivot_ne_zero
        · exact stabilized.stable.pivot_normalized
        · intro column
          simp
        · intro row
          simp
        · simpa using lower.value.isSmith
        · intro row column
          rw [adjoinPivot_succ_succ, ← lower.value.equation]
          exact dvd_matrix_mul_of_left
            (dvd_matrix_mul_of_right
              stabilized.stable.pivotDividesLower) row column }
  exact
    { value
      charges := final.charges
      controlTrace :=
        { passes := stabilized.passes + lower.controlTrace.passes
          injections := stabilized.injections + lower.controlTrace.injections }
      trace_wellFormed := final.trace_wellFormed
      chargeOwnership := final.chargeOwnership }

public theorem assembleExecution_value {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (stabilized : StabilizationExecution A)
    (lower : SmithExecution
      (lowerRight stabilized.certificate.value.result)) :
    (assembleExecution stabilized lower).value =
      assemble stabilized.value lower.value := by
  apply snfResultFin_ext_data
  · simp only [assembleExecution, assemble, StabilizationExecution.value]
    rw [composeExecution_value]
  · simp only [assembleExecution, assemble, StabilizationExecution.value]
    rw [composeExecution_value]
  · simp only [assembleExecution, assemble, StabilizationExecution.value]
    rw [composeExecution_value]
  · simp only [assembleExecution, assemble, StabilizationExecution.value]
    rw [composeExecution_value]
  · simp only [assembleExecution, assemble, StabilizationExecution.value]
    rw [composeExecution_value]

private theorem smith_data_eq_of_matrix_eq {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Int) (matrixEq : A = B)
    (hdetA : A.det ≠ 0) (hdetB : B.det ≠ 0) :
    let left := smith A hdetA
    let right := smith B hdetB
    left.U = right.U ∧
      left.U_cert.inverse = right.U_cert.inverse ∧
      left.S = right.S ∧
      left.V = right.V ∧
      left.V_cert.inverse = right.V_cert.inverse := by
  subst B
  simp

private theorem assemble_data_eq {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (left right : Stabilization A)
    (certificate_eq : left.certificate = right.certificate)
    (lowerLeft : SNFResultFin (lowerRight left.certificate.result))
    (lowerRightResult : SNFResultFin
      (lowerRight right.certificate.result))
    (u_eq : lowerLeft.U = lowerRightResult.U)
    (uinv_eq :
      lowerLeft.U_cert.inverse = lowerRightResult.U_cert.inverse)
    (s_eq : lowerLeft.S = lowerRightResult.S)
    (v_eq : lowerLeft.V = lowerRightResult.V)
    (vinv_eq :
      lowerLeft.V_cert.inverse = lowerRightResult.V_cert.inverse) :
    assemble left lowerLeft = assemble right lowerRightResult := by
  cases left with
  | mk leftCertificate leftStable leftPasses leftInjections =>
      cases right with
      | mk rightCertificate rightStable rightPasses rightInjections =>
          dsimp only at certificate_eq
          subst rightCertificate
          apply snfResultFin_ext_data
          · simp only [assemble, liftLowerCertificate, compose]
            rw [u_eq]
          · simp only [assemble, liftLowerCertificate, compose,
              MatrixInverseCertificate.mul, leadingLiftCertificate]
            rw [uinv_eq]
          · simp only [assemble, liftLowerCertificate, compose]
            rw [s_eq]
          · simp only [assemble, liftLowerCertificate, compose]
            rw [v_eq]
          · simp only [assemble, liftLowerCertificate, compose,
              MatrixInverseCertificate.mul, leadingLiftCertificate]
            rw [vinv_eq]

/--
Value-producing outer recursion.  Dimension decreases structurally; each
lower-right input is the preceding stabilization execution's result.
-/
@[expose] public def smithExecution : {n : Nat} →
    (A : Matrix (Fin n) (Fin n) Int) → A.det ≠ 0 → SmithExecution A
  | 0, A, _hdet =>
      { value :=
          { U := 1
            U_cert := MatrixInverseCertificate.one
            S := A
            V := 1
            V_cert := MatrixInverseCertificate.one
            equation := NormalForms.Matrix.Constructive.one_mul_mul_one A
            isSmith := IsSmithNormalFormFin.emptyRows A }
        charges := []
        controlTrace := { passes := 0, injections := 0 }
        trace_wellFormed := by simp [ArithmeticChargeListWellFormed]
        chargeOwnership := by simp }
  | _n + 1, A, hdet =>
      let stabilized := stabilizeExecution A hdet
      let transformed := stabilized.certificate.value.result
      let transformedDet : transformed.det ≠ 0 :=
        result_det_ne_zero stabilized.certificate.value hdet
      let lowerDet : (lowerRight transformed).det ≠ 0 :=
        stable_lowerRight_det_ne_zero transformed stabilized.stable
          transformedDet
      assembleExecution stabilized
        (smithExecution (lowerRight transformed) lowerDet)

/-- Every runtime Smith result replays both explicit certificate directions. -/
public theorem smithExecution_replay {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    let run := (smithExecution A hdet).value
    run.U * A * run.V = run.S ∧
      run.U_cert.inverse * run.S * run.V_cert.inverse = A := by
  let run := (smithExecution A hdet).value
  exact
    ⟨run.equation,
      inverse_equation
        { U := run.U
          U_cert := run.U_cert
          result := run.S
          V := run.V
          V_cert := run.V_cert
          equation := run.equation }⟩

/-- The value-producing dimension recursion refines the pure algorithm. -/
public theorem smithExecution_value {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithExecution A hdet).value = smith A hdet := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [smithExecution, smith, assembleExecution_value]
      let executedStabilized := stabilizeExecution A hdet
      let pureStabilized := stabilize A hdet
      have stabilizedCertificate :
          executedStabilized.certificate.value =
            pureStabilized.certificate :=
        stabilizeExecution_replay A hdet
      let executedLower :=
        lowerRight executedStabilized.certificate.value.result
      let pureLower :=
        lowerRight pureStabilized.certificate.result
      have lowerMatrix : executedLower = pureLower :=
        congrArg lowerRight <|
          congrArg (fun certificate ↦ certificate.result)
            stabilizedCertificate
      let executedTransformedDet :=
        result_det_ne_zero executedStabilized.certificate.value hdet
      let executedLowerDet :=
        stable_lowerRight_det_ne_zero
          executedStabilized.certificate.value.result
          executedStabilized.stable executedTransformedDet
      let pureTransformedDet :=
        pureStabilized.result_det_ne_zero hdet
      let pureLowerDet :=
        stable_lowerRight_det_ne_zero
          pureStabilized.certificate.result pureStabilized.stable
          pureTransformedDet
      have lowerExecution :
          (smithExecution executedLower executedLowerDet).value =
            smith executedLower executedLowerDet :=
        ih executedLower executedLowerDet
      have lowerPureData :=
        smith_data_eq_of_matrix_eq executedLower pureLower lowerMatrix
          executedLowerDet pureLowerDet
      apply assemble_data_eq
        executedStabilized.value pureStabilized stabilizedCertificate
      · exact (congrArg (fun result ↦ result.U) lowerExecution).trans
          lowerPureData.1
      · exact
          (congrArg (fun result ↦ result.U_cert.inverse)
            lowerExecution).trans lowerPureData.2.1
      · exact (congrArg (fun result ↦ result.S) lowerExecution).trans
          lowerPureData.2.2.1
      · exact (congrArg (fun result ↦ result.V) lowerExecution).trans
          lowerPureData.2.2.2.1
      · exact
          (congrArg (fun result ↦ result.V_cert.inverse)
            lowerExecution).trans lowerPureData.2.2.2.2

/-- The execution value has the full strong Smith contract. -/
public theorem smithExecution_contract {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    let run := (smithExecution A hdet).value
    run.U * A * run.V = run.S ∧
      run.U_cert.inverse * run.S * run.V_cert.inverse = A ∧
      IsSmithNormalFormFin run.S :=
  ⟨(smithExecution_replay A hdet).1,
    (smithExecution_replay A hdet).2,
    (smithExecution A hdet).value.isSmith⟩

public theorem smithExecution_inverse_identities {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    let run := (smithExecution A hdet).value
    run.U_cert.inverse * run.U = 1 ∧ run.U * run.U_cert.inverse = 1 ∧
      run.V_cert.inverse * run.V = 1 ∧ run.V * run.V_cert.inverse = 1 := by
  let run := (smithExecution A hdet).value
  exact ⟨run.U_cert.left_inv, run.U_cert.right_inv,
    run.V_cert.left_inv, run.V_cert.right_inv⟩

/-- The executed Smith matrix equals the canonical core reference. -/
public theorem smithExecution_eq_reference {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithExecution A hdet).value.S = (smithNormalFormFin A).S := by
  let result := (smithExecution A hdet).value
  let reference := smithNormalFormFin A
  let left := reference.U * result.U_cert.inverse
  let right := result.V_cert.inverse * reference.V
  have leftCertificate : MatrixInverseCertificate left :=
    reference.U_cert.mul result.U_cert.symm
  have rightCertificate : MatrixInverseCertificate right :=
    result.V_cert.symm.mul reference.V_cert
  apply Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
    result.isSmith reference.isSmith leftCertificate.unimodular
      rightCertificate.unimodular
  calc
    left * result.S * right =
        reference.U *
          (result.U_cert.inverse * result.S *
            result.V_cert.inverse) * reference.V := by
      simp only [left, right, Matrix.mul_assoc]
    _ = reference.U * A * reference.V := by
      rw [(smithExecution_replay A hdet).2]
    _ = reference.S := reference.equation

/-- Executed and pure Kannan--Bachem runs have the same canonical Smith matrix. -/
public theorem smithExecution_eq_smith_matrix {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithExecution A hdet).value.S = (smith A hdet).S :=
  (smithExecution_eq_reference A hdet).trans (smith_eq_reference A hdet).symm

public theorem smithExecution_trace_wellFormed {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    ArithmeticChargeListWellFormed (smithExecution A hdet).charges :=
  (smithExecution A hdet).trace_wellFormed

public theorem smithExecution_chargeOwnership {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    ∀ charge ∈ (smithExecution A hdet).charges, charge.WellFormed :=
  (smithExecution A hdet).chargeOwnership

/-- Cost endpoint: the exact fold of the execution's primitive leaves. -/
@[expose] public def smithWithCost {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    NormalForms.Research.BitCost.WithCost (SNFResultFin A) :=
  let run := smithExecution A hdet
  { value := run.value
    cost := traceBitCost run.charges }

/-- Macro-operation endpoint derived from the same leaf trace. -/
@[expose] public def smithOperationCount {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    ArithmeticOperationCount :=
  traceOperationCount (smithExecution A hdet).charges

public theorem smithWithCost_cost_eq_traceBitCost {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithWithCost A hdet).cost =
      traceBitCost (smithExecution A hdet).charges :=
  rfl

public theorem smithOperationCount_eq_traceOperationCount {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    smithOperationCount A hdet =
      traceOperationCount (smithExecution A hdet).charges :=
  rfl

end NormalForms.Research.KannanBachem
