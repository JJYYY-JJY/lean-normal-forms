/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Clear
public import NormalForms.Research.KannanBachem.Smith.Totality

/-! # Single Instrumented Pivot Stabilization -/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Research.BitCost
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Add control-flow arithmetic before an existing certificate execution. -/
@[expose] public def CertificateExecution.prependCharges {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (chargesBefore : List KannanBachemArithmeticCharge)
    (chargesBeforeWellFormed : ArithmeticChargeListWellFormed chargesBefore)
    (execution : CertificateExecution A) :
    CertificateExecution A :=
  { value := execution.value
    charges := chargesBefore ++ execution.charges
    trace_wellFormed :=
      chargesBeforeWellFormed.append execution.trace_wellFormed
    chargeOwnership := List.forall_iff_forall_mem.mp <|
      chargesBeforeWellFormed.append execution.trace_wellFormed }

/-- Add control-flow arithmetic after an existing certificate execution. -/
@[expose] public def CertificateExecution.appendCharges {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (execution : CertificateExecution A)
    (suffix : List KannanBachemArithmeticCharge)
    (suffixWellFormed : ArithmeticChargeListWellFormed suffix) :
    CertificateExecution A :=
  { value := execution.value
    charges := execution.charges ++ suffix
    trace_wellFormed := execution.trace_wellFormed.append suffixWellFormed
    chargeOwnership := List.forall_iff_forall_mem.mp <|
      execution.trace_wellFormed.append suffixWellFormed }

@[simp] public theorem CertificateExecution.prependCharges_value {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (chargesBefore : List KannanBachemArithmeticCharge)
    (chargesBeforeWellFormed : ArithmeticChargeListWellFormed chargesBefore)
    (execution : CertificateExecution A) :
    (execution.prependCharges
      chargesBefore chargesBeforeWellFormed).value = execution.value :=
  rfl

@[simp] public theorem CertificateExecution.appendCharges_value {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (execution : CertificateExecution A)
    (suffix : List KannanBachemArithmeticCharge)
    (suffixWellFormed : ArithmeticChargeListWellFormed suffix) :
    (execution.appendCharges suffix suffixWellFormed).value = execution.value :=
  rfl

/-- Runtime output of one instrumented stabilization. -/
public structure StabilizationExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) where
  certificate : CertificateExecution A
  stable : StablePivot certificate.value.result
  passes : Nat
  injections : Nat

namespace StabilizationExecution

@[expose] public def value {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (execution : StabilizationExecution A) : Stabilization A :=
  { certificate := execution.certificate.value
    stable := execution.stable
    passes := execution.passes
    injections := execution.injections }

@[expose] public def charges {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (execution : StabilizationExecution A) :
    List KannanBachemArithmeticCharge :=
  execution.certificate.charges

public theorem trace_wellFormed {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (execution : StabilizationExecution A) :
    ArithmeticChargeListWellFormed execution.charges :=
  execution.certificate.trace_wellFormed

public theorem chargeOwnership {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (execution : StabilizationExecution A) :
    ∀ charge ∈ execution.charges, charge.WellFormed :=
  execution.certificate.chargeOwnership

end StabilizationExecution

/--
Instrumented inner loop.  Its recursive inputs and branches come from the
preceding execution values; the termination measure is the pivot binary size.
-/
@[expose] public def stabilizeFromExecution {n : Nat} :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) →
      A.det ≠ 0 → A 0 0 ≠ 0 →
        A 0 0 = _root_.normalize (A 0 0) → FirstRowCleared A →
          StabilizationExecution A
  | A, hdet, hpivot, hnormalized, hrow =>
      let below := firstUndivisibleBelowWithCost A
      match hbadColumn : below.value with
      | some row =>
          let current := passExecution A hdet
          have shape :
              current.value.result 0 0 ≠ 0 ∧
                current.value.result 0 0 =
                  _root_.normalize (current.value.result 0 0) ∧
                FirstRowCleared current.value.result := by
            rw [passExecution_value]
            exact pass_shape A hdet
          let next := stabilizeFromExecution current.value.result
            (result_det_ne_zero current.value hdet)
            shape.1 shape.2.1 shape.2.2
          let prefixed := current.prependCharges below.charges
            below.trace_wellFormed
          let composed := composeExecution prefixed next.certificate
          { certificate := composed
            stable := next.stable
            passes := next.passes + 1
            injections := next.injections }
      | none =>
          have pureNoBadColumn : firstUndivisibleBelow? A = none :=
            (firstUndivisibleBelowWithCost_value A).symm.trans hbadColumn
          let hdiv := firstUndivisibleBelow?_eq_none A pureNoBadColumn
          let cleared := clearExecution A hpivot hdiv
          have hclearedColumn : FirstColumnCleared cleared.value.result := by
            rw [clearExecution_value]
            exact clearDivisibleFirstColumn_firstColumnCleared A hdiv
          have hclearedRow : FirstRowCleared cleared.value.result := by
            rw [clearExecution_value]
            exact clearDivisibleFirstColumn_firstRowCleared A hrow
          let lower := firstUndivisibleLowerWithCost cleared.value.result
          match hbadLower : lower.value with
          | none =>
              have pureNoBadLower :
                  firstUndivisibleLower? cleared.value.result = none :=
                (firstUndivisibleLowerWithCost_value
                  cleared.value.result).symm.trans hbadLower
              let controlled := (cleared.prependCharges below.charges
                below.trace_wellFormed).appendCharges lower.charges
                  lower.trace_wellFormed
              { certificate := controlled
                stable :=
                  { pivot_ne_zero := by
                      change cleared.value.result 0 0 ≠ 0
                      rw [show cleared.value.result 0 0 = A 0 0 by
                        rw [clearExecution_value]
                        exact clearDivisibleFirstColumn_pivot A]
                      exact hpivot
                    pivot_normalized := by
                      change
                        cleared.value.result 0 0 =
                          _root_.normalize (cleared.value.result 0 0)
                      rw [show cleared.value.result 0 0 = A 0 0 by
                        rw [clearExecution_value]
                        exact clearDivisibleFirstColumn_pivot A]
                      exact hnormalized
                    firstRowCleared := hclearedRow
                    firstColumnCleared := hclearedColumn
                    pivotDividesLower :=
                      firstUndivisibleLower?_eq_none
                        cleared.value.result pureNoBadLower }
                passes := 0
                injections := 0 }
          | some position =>
              let injection := injectExecution
                cleared.value.result position.2
              let controlled := (cleared.prependCharges below.charges
                below.trace_wellFormed).appendCharges lower.charges
                  lower.trace_wellFormed
              let accumulated := composeExecution controlled injection
              let accumulatedDet := result_det_ne_zero accumulated.value hdet
              let current := passExecution accumulated.value.result accumulatedDet
              have shape :
                  current.value.result 0 0 ≠ 0 ∧
                    current.value.result 0 0 =
                      _root_.normalize (current.value.result 0 0) ∧
                    FirstRowCleared current.value.result := by
                rw [passExecution_value]
                exact pass_shape accumulated.value.result accumulatedDet
              let next := stabilizeFromExecution current.value.result
                (result_det_ne_zero current.value accumulatedDet)
                shape.1 shape.2.1 shape.2.2
              let tail := composeExecution current next.certificate
              let composed := composeExecution accumulated tail
              { certificate := composed
                stable := next.stable
                passes := next.passes + 1
                injections := next.injections + 1 }
termination_by A _ _ _ _ => (A 0 0).natAbs.size
decreasing_by
  · have pureBadColumn :
        firstUndivisibleBelow? A = some row :=
      (firstUndivisibleBelowWithCost_value A).symm.trans hbadColumn
    have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
      A hdet hpivot row.succ
      (firstUndivisibleBelow?_some_not_dvd A pureBadColumn)
    simpa [passExecution_value] using decrease
  · have pureBadLower :
        firstUndivisibleLower? cleared.value.result = some position :=
      (firstUndivisibleLowerWithCost_value
        cleared.value.result).symm.trans hbadLower
    have accumulatedResult :
        accumulated.value.result =
          (injectLowerWitness cleared.value.result position.2).result := by
      calc
        accumulated.value.result = injection.value.result := by
          simpa only [compose] using
            congrArg (fun certificate ↦ certificate.result)
            (composeExecution_value controlled injection)
        _ = (injectLowerWitness cleared.value.result position.2).result :=
          congrArg (fun certificate ↦ certificate.result)
            (injectExecution_value cleared.value.result position.2)
    have accumulatedPivot : accumulated.value.result 0 0 = A 0 0 := by
      rw [accumulatedResult]
      exact
        (injectLowerWitness_pivot cleared.value.result
          position.2 hclearedRow).trans (by
            rw [clearExecution_value]
            exact clearDivisibleFirstColumn_pivot A)
    have target :
        accumulated.value.result position.1.succ 0 =
          cleared.value.result position.1.succ position.2.succ := by
      rw [accumulatedResult]
      exact injectLowerWitness_target cleared.value.result
        position.1 position.2 hclearedColumn
    have hnot : ¬ accumulated.value.result 0 0 ∣
        accumulated.value.result position.1.succ 0 := by
      rw [accumulatedPivot, target]
      have original := firstUndivisibleLower?_some_not_dvd
        cleared.value.result pureBadLower
      rw [← show cleared.value.result 0 0 = A 0 0 by
        rw [clearExecution_value]
        exact clearDivisibleFirstColumn_pivot A]
      exact original
    have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
      accumulated.value.result accumulatedDet
      (by simpa [accumulatedPivot] using hpivot) position.1.succ hnot
    simpa [passExecution_value, accumulatedPivot] using decrease

/-- Mandatory first pass followed by the single instrumented inner recursion. -/
@[expose] public def stabilizeExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) : StabilizationExecution A :=
  let initial := passExecution A hdet
  have shape :
      initial.value.result 0 0 ≠ 0 ∧
        initial.value.result 0 0 =
          _root_.normalize (initial.value.result 0 0) ∧
        FirstRowCleared initial.value.result := by
    rw [passExecution_value]
    exact pass_shape A hdet
  let rest := stabilizeFromExecution initial.value.result
    (result_det_ne_zero initial.value hdet)
    shape.1 shape.2.1 shape.2.2
  let composed := composeExecution initial rest.certificate
  { certificate := composed
    stable := rest.stable
    passes := rest.passes + 1
    injections := rest.injections }

public theorem stabilization_ext_data {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (left right : Stabilization A)
    (certificate_eq : left.certificate = right.certificate)
    (passes_eq : left.passes = right.passes)
    (injections_eq : left.injections = right.injections) :
    left = right := by
  cases left
  cases right
  simp_all
private theorem stabilizeFrom_certificate_data_eq_of_matrix_eq {n : Nat}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (matrixEq : A = B)
    (hdetA : A.det ≠ 0) (hpivotA : A 0 0 ≠ 0)
    (hnormalizedA : A 0 0 = _root_.normalize (A 0 0))
    (hrowA : FirstRowCleared A)
    (hdetB : B.det ≠ 0) (hpivotB : B 0 0 ≠ 0)
    (hnormalizedB : B 0 0 = _root_.normalize (B 0 0))
    (hrowB : FirstRowCleared B) :
    let left :=
      (stabilizeFrom A hdetA hpivotA hnormalizedA hrowA).certificate
    let right :=
      (stabilizeFrom B hdetB hpivotB hnormalizedB hrowB).certificate
    left.U = right.U ∧
      left.U_cert.inverse = right.U_cert.inverse ∧
      left.result = right.result ∧
      left.V = right.V ∧
      left.V_cert.inverse = right.V_cert.inverse := by
  subst B
  simp

private theorem pass_data_eq_of_matrix_eq {n : Nat}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (matrixEq : A = B) (hdetA : A.det ≠ 0) (hdetB : B.det ≠ 0) :
    let left := pass A hdetA
    let right := pass B hdetB
    left.U = right.U ∧
      left.U_cert.inverse = right.U_cert.inverse ∧
      left.result = right.result ∧
      left.V = right.V ∧
      left.V_cert.inverse = right.V_cert.inverse := by
  subst B
  simp

private theorem stabilizeFrom_certificate_eq_of_badColumn {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A) (row : Fin n)
    (hbad : firstUndivisibleBelow? A = some row) :
    (stabilizeFrom A hdet hpivot hnormalized hrow).certificate =
      let current := pass A hdet
      let shape := pass_shape A hdet
      let next := stabilizeFrom current.result
        (pass_result_det_ne_zero A hdet) shape.1 shape.2.1 shape.2.2
      compose current next.certificate := by
  rw [stabilizeFrom.eq_1]
  split
  next actual hactual =>
    have actualEq : actual = row :=
      Option.some.inj (hactual.symm.trans hbad)
    subst actual
    rfl
  next hnone =>
    cases hbad.symm.trans hnone

private theorem stabilizeFrom_certificate_eq_of_stable {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A)
    (hcolumn : firstUndivisibleBelow? A = none)
    (hlower :
      firstUndivisibleLower? (clearDivisibleFirstColumn A).result = none) :
    (stabilizeFrom A hdet hpivot hnormalized hrow).certificate =
      clearDivisibleFirstColumn A := by
  rw [stabilizeFrom.eq_1]
  split
  next _ hsome =>
    cases hcolumn.symm.trans hsome
  next _hnone =>
    dsimp only
    split
    next _hnone =>
      rfl
    next _ hsome =>
      cases hlower.symm.trans hsome

private theorem stabilizeFrom_certificate_eq_of_injection {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A)
    (hcolumn : firstUndivisibleBelow? A = none)
    (position : Fin n × Fin n)
    (hlower :
      firstUndivisibleLower? (clearDivisibleFirstColumn A).result =
        some position) :
    (stabilizeFrom A hdet hpivot hnormalized hrow).certificate =
      let cleared := clearDivisibleFirstColumn A
      let injection := injectLowerWitness cleared.result position.2
      let accumulated := compose cleared injection
      let accumulatedDet := result_det_ne_zero accumulated hdet
      let current := pass accumulated.result accumulatedDet
      let shape := pass_shape accumulated.result accumulatedDet
      let next := stabilizeFrom current.result
        (pass_result_det_ne_zero accumulated.result accumulatedDet)
        shape.1 shape.2.1 shape.2.2
      compose accumulated (compose current next.certificate) := by
  rw [stabilizeFrom.eq_1]
  split
  next _ hsome =>
    cases hcolumn.symm.trans hsome
  next _hnone =>
    dsimp only
    split
    next hnone =>
      cases hlower.symm.trans hnone
    next actual hactual =>
      have actualEq : actual = position :=
        Option.some.inj (hactual.symm.trans hlower)
      subst actual
      rfl

/-- The instrumented inner recursion refines the existing total semantics. -/
public theorem stabilizeFromExecution_replay {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) (hpivot : A 0 0 ≠ 0)
    (hnormalized : A 0 0 = _root_.normalize (A 0 0))
    (hrow : FirstRowCleared A) :
    (stabilizeFromExecution A hdet hpivot hnormalized hrow).certificate.value =
      (stabilizeFrom A hdet hpivot hnormalized hrow).certificate := by
  generalize measureEq : (A 0 0).natAbs.size = measure
  induction measure using Nat.strong_induction_on generalizing A with
  | h measure ih =>
      rw [stabilizeFromExecution.eq_1]
      split
      next row hbadColumn =>
        have pureBadColumn :
            firstUndivisibleBelow? A = some row :=
          (firstUndivisibleBelowWithCost_value A).symm.trans hbadColumn
        rw [stabilizeFrom_certificate_eq_of_badColumn
          A hdet hpivot hnormalized hrow row pureBadColumn]
        dsimp only
        have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
          A hdet hpivot row.succ
            (firstUndivisibleBelow?_some_not_dvd A pureBadColumn)
        have nextReplay := ih _ (by simpa [measureEq,
            passExecution_value] using decrease)
          (passExecution A hdet).value.result
          (result_det_ne_zero (passExecution A hdet).value hdet)
          (by
            rw [passExecution_value]
            exact (pass_shape A hdet).1)
          (by
            rw [passExecution_value]
            exact (pass_shape A hdet).2.1)
          (by
            rw [passExecution_value]
            exact (pass_shape A hdet).2.2)
          rfl
        have passEq :
            (passExecution A hdet).value = pass A hdet :=
          passExecution_value A hdet
        have resultEq :
            (passExecution A hdet).value.result = (pass A hdet).result :=
          congrArg (fun certificate ↦ certificate.result) passEq
        have restData :=
          stabilizeFrom_certificate_data_eq_of_matrix_eq
            (passExecution A hdet).value.result (pass A hdet).result resultEq
            (result_det_ne_zero (passExecution A hdet).value hdet)
            (by rw [passEq]; exact (pass_shape A hdet).1)
            (by rw [passEq]; exact (pass_shape A hdet).2.1)
            (by rw [passEq]; exact (pass_shape A hdet).2.2)
            (pass_result_det_ne_zero A hdet)
            (pass_shape A hdet).1 (pass_shape A hdet).2.1
            (pass_shape A hdet).2.2
        rw [composeExecution_value]
        apply twoSidedCertificate_ext_data
        · simp only [compose]
          rw [nextReplay, restData.1,
            CertificateExecution.prependCharges_value, passEq]
        · simp only [compose, MatrixInverseCertificate.mul]
          rw [nextReplay, restData.2.1,
            CertificateExecution.prependCharges_value, passEq]
        · simp only [compose]
          exact (congrArg (fun certificate ↦ certificate.result)
            nextReplay).trans restData.2.2.1
        · simp only [compose]
          rw [nextReplay, restData.2.2.2.1,
            CertificateExecution.prependCharges_value, passEq]
        · simp only [compose, MatrixInverseCertificate.mul]
          rw [nextReplay, restData.2.2.2.2,
            CertificateExecution.prependCharges_value, passEq]
      next hbadColumn =>
        have pureNoBadColumn :
            firstUndivisibleBelow? A = none :=
          (firstUndivisibleBelowWithCost_value A).symm.trans hbadColumn
        dsimp only
        let hdiv := firstUndivisibleBelow?_eq_none A
          pureNoBadColumn
        let cleared := clearExecution A hpivot hdiv
        have clearedValue :
            cleared.value = clearDivisibleFirstColumn A :=
          clearExecution_value A hpivot hdiv
        split
        next hbadLower =>
          have pureNoBadLower :
              firstUndivisibleLower? (clearDivisibleFirstColumn A).result =
                none := by
            have actual :
                firstUndivisibleLower? cleared.value.result = none :=
              (firstUndivisibleLowerWithCost_value
                cleared.value.result).symm.trans hbadLower
            simpa only [clearedValue] using actual
          rw [stabilizeFrom_certificate_eq_of_stable
            A hdet hpivot hnormalized hrow pureNoBadColumn pureNoBadLower]
          exact clearedValue
        next position hbadLower =>
          have pureBadLowerReference :
              firstUndivisibleLower? (clearDivisibleFirstColumn A).result =
                some position := by
            have actual :
                firstUndivisibleLower? cleared.value.result = some position :=
              (firstUndivisibleLowerWithCost_value
                cleared.value.result).symm.trans hbadLower
            simpa only [clearedValue] using actual
          rw [stabilizeFrom_certificate_eq_of_injection
            A hdet hpivot hnormalized hrow pureNoBadColumn position
            pureBadLowerReference]
          let injection := injectExecution cleared.value.result position.2
          let controlled :=
            (cleared.prependCharges
              (firstUndivisibleBelowWithCost A).charges
              (firstUndivisibleBelowWithCost A).trace_wellFormed).appendCharges
                (firstUndivisibleLowerWithCost cleared.value.result).charges
                (firstUndivisibleLowerWithCost
                  cleared.value.result).trace_wellFormed
          let accumulated := composeExecution controlled injection
          let accumulatedDet := result_det_ne_zero accumulated.value hdet
          have pureBadLower :
              firstUndivisibleLower? cleared.value.result = some position :=
            (firstUndivisibleLowerWithCost_value
              cleared.value.result).symm.trans hbadLower
          have accumulatedValue :
              accumulated.value =
                compose (clearDivisibleFirstColumn A)
                  (injectLowerWitness
                    (clearDivisibleFirstColumn A).result position.2) := by
            have injectionValue :=
              injectExecution_value cleared.value.result position.2
            have clearedResult :
                cleared.value.result =
                  (clearDivisibleFirstColumn A).result :=
              congrArg (fun certificate ↦ certificate.result) clearedValue
            rw [composeExecution_value]
            apply twoSidedCertificate_ext_data
            · simp only [compose]
              rw [injectionValue]
              simp only [injectLowerWitness, Matrix.one_mul]
              rw [
                CertificateExecution.appendCharges_value,
                CertificateExecution.prependCharges_value, clearedValue]
            · simp only [compose, MatrixInverseCertificate.mul]
              rw [injectionValue]
              simp only [injectLowerWitness]
              rw [
                CertificateExecution.appendCharges_value,
                CertificateExecution.prependCharges_value, clearedValue]
            · simp only [compose]
              rw [injectionValue]
              exact congrArg
                (fun matrix ↦
                  (injectLowerWitness matrix position.2).result)
                clearedResult
            · simp only [compose]
              rw [injectionValue]
              simp only [injectLowerWitness]
              rw [
                CertificateExecution.appendCharges_value,
                CertificateExecution.prependCharges_value, clearedValue]
            · simp only [compose, MatrixInverseCertificate.mul]
              rw [injectionValue]
              simp only [injectLowerWitness]
              rw [
                CertificateExecution.appendCharges_value,
                CertificateExecution.prependCharges_value, clearedValue]
          have accumulatedPivot :
              accumulated.value.result 0 0 = A 0 0 := by
            rw [accumulatedValue]
            exact (injectLowerWitness_pivot
              (clearDivisibleFirstColumn A).result position.2
              (clearDivisibleFirstColumn_firstRowCleared A hrow)).trans
                (clearDivisibleFirstColumn_pivot A)
          have target :
              accumulated.value.result position.1.succ 0 =
                cleared.value.result position.1.succ position.2.succ := by
            have resultEq := congrArg (fun certificate ↦ certificate.result)
              accumulatedValue
            rw [resultEq, clearedValue]
            exact injectLowerWitness_target
              (clearDivisibleFirstColumn A).result position.1 position.2
              (clearDivisibleFirstColumn_firstColumnCleared A hdiv)
          have hnot : ¬ accumulated.value.result 0 0 ∣
              accumulated.value.result position.1.succ 0 := by
            rw [accumulatedPivot, target, clearedValue,
              ← clearDivisibleFirstColumn_pivot A]
            exact firstUndivisibleLower?_some_not_dvd
              (clearDivisibleFirstColumn A).result (by
                simpa [clearedValue] using pureBadLower)
          have decrease := pass_pivot_natSize_lt_of_not_dvd_entry
            accumulated.value.result accumulatedDet
            (by simpa [accumulatedPivot] using hpivot)
            position.1.succ hnot
          have nextReplay := ih _ (by
              simpa [measureEq, accumulatedPivot, passExecution_value]
                using decrease)
            (passExecution accumulated.value.result accumulatedDet).value.result
            (result_det_ne_zero
              (passExecution accumulated.value.result accumulatedDet).value
              accumulatedDet)
            (by
              rw [passExecution_value]
              exact (pass_shape accumulated.value.result accumulatedDet).1)
            (by
              rw [passExecution_value]
              exact (pass_shape accumulated.value.result accumulatedDet).2.1)
            (by
              rw [passExecution_value]
              exact (pass_shape accumulated.value.result accumulatedDet).2.2)
            rfl
          let pureAccumulated :=
            compose (clearDivisibleFirstColumn A)
              (injectLowerWitness
                (clearDivisibleFirstColumn A).result position.2)
          let pureAccumulatedDet :=
            result_det_ne_zero pureAccumulated hdet
          let executedCurrent :=
            (passExecution accumulated.value.result accumulatedDet).value
          let pureCurrent :=
            pass pureAccumulated.result pureAccumulatedDet
          have accumulatedResult :
              accumulated.value.result = pureAccumulated.result :=
            congrArg (fun certificate ↦ certificate.result) accumulatedValue
          have executedCurrentValue :
              executedCurrent =
                pass accumulated.value.result accumulatedDet :=
            passExecution_value accumulated.value.result accumulatedDet
          have pureCurrentData :=
            pass_data_eq_of_matrix_eq accumulated.value.result
              pureAccumulated.result accumulatedResult accumulatedDet
              pureAccumulatedDet
          have currentU : executedCurrent.U = pureCurrent.U :=
            (congrArg (fun certificate ↦ certificate.U)
              executedCurrentValue).trans pureCurrentData.1
          have currentUinv :
              executedCurrent.U_cert.inverse =
                pureCurrent.U_cert.inverse :=
            (congrArg (fun certificate ↦ certificate.U_cert.inverse)
              executedCurrentValue).trans pureCurrentData.2.1
          have currentResult :
              executedCurrent.result = pureCurrent.result :=
            (congrArg (fun certificate ↦ certificate.result)
              executedCurrentValue).trans pureCurrentData.2.2.1
          have currentV : executedCurrent.V = pureCurrent.V :=
            (congrArg (fun certificate ↦ certificate.V)
              executedCurrentValue).trans pureCurrentData.2.2.2.1
          have currentVinv :
              executedCurrent.V_cert.inverse =
                pureCurrent.V_cert.inverse :=
            (congrArg (fun certificate ↦ certificate.V_cert.inverse)
              executedCurrentValue).trans pureCurrentData.2.2.2.2
          have nextData :=
            stabilizeFrom_certificate_data_eq_of_matrix_eq
              executedCurrent.result pureCurrent.result currentResult
              (result_det_ne_zero executedCurrent accumulatedDet)
              (by rw [executedCurrentValue]; exact
                (pass_shape accumulated.value.result accumulatedDet).1)
              (by rw [executedCurrentValue]; exact
                (pass_shape accumulated.value.result accumulatedDet).2.1)
              (by rw [executedCurrentValue]; exact
                (pass_shape accumulated.value.result accumulatedDet).2.2)
              (pass_result_det_ne_zero
                pureAccumulated.result pureAccumulatedDet)
              (pass_shape pureAccumulated.result pureAccumulatedDet).1
              (pass_shape pureAccumulated.result pureAccumulatedDet).2.1
              (pass_shape pureAccumulated.result pureAccumulatedDet).2.2
          simp only [composeExecution_value]
          apply twoSidedCertificate_ext_data
          · simp only [compose]
            rw [nextReplay, nextData.1, currentU, accumulatedValue]
            simp only [compose, Matrix.mul_assoc]
            rfl
          · simp only [compose, MatrixInverseCertificate.mul]
            rw [nextReplay, nextData.2.1, currentUinv, accumulatedValue]
            simp only [compose, MatrixInverseCertificate.mul, Matrix.mul_assoc]
            rfl
          · simp only [compose]
            exact (congrArg (fun certificate ↦ certificate.result)
              nextReplay).trans nextData.2.2.1
          · simp only [compose]
            rw [nextReplay, nextData.2.2.2.1, currentV,
              accumulatedValue]
            simp only [compose, Matrix.mul_assoc]
            rfl
          · simp only [compose, MatrixInverseCertificate.mul]
            rw [nextReplay, nextData.2.2.2.2, currentVinv,
              accumulatedValue]
            simp only [compose, MatrixInverseCertificate.mul, Matrix.mul_assoc]
            rfl

/-- The mandatory-pass execution refines total stabilization. -/
public theorem stabilizeExecution_replay {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    (stabilizeExecution A hdet).certificate.value =
      (stabilize A hdet).certificate := by
  simp only [stabilizeExecution, stabilize, composeExecution_value]
  rw [stabilizeFromExecution_replay]
  let executedPass := (passExecution A hdet).value
  let purePass := pass A hdet
  let executedRest := stabilizeFrom executedPass.result
    (result_det_ne_zero executedPass hdet)
    (by simpa [executedPass, passExecution_value] using (pass_shape A hdet).1)
    (by simpa [executedPass, passExecution_value] using (pass_shape A hdet).2.1)
    (by simpa [executedPass, passExecution_value] using (pass_shape A hdet).2.2)
  let pureRest := stabilizeFrom purePass.result
    (pass_result_det_ne_zero A hdet)
    (pass_shape A hdet).1 (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
  have passEq : executedPass = purePass := passExecution_value A hdet
  have resultEq : executedPass.result = purePass.result :=
    congrArg (fun certificate ↦ certificate.result) passEq
  have restData :=
    stabilizeFrom_certificate_data_eq_of_matrix_eq
      executedPass.result purePass.result resultEq
      (result_det_ne_zero executedPass hdet)
      (by simpa [executedPass, passExecution_value] using (pass_shape A hdet).1)
      (by simpa [executedPass, passExecution_value] using (pass_shape A hdet).2.1)
      (by simpa [executedPass, passExecution_value] using (pass_shape A hdet).2.2)
      (pass_result_det_ne_zero A hdet)
      (pass_shape A hdet).1 (pass_shape A hdet).2.1 (pass_shape A hdet).2.2
  change compose executedPass executedRest.certificate =
    compose purePass pureRest.certificate
  apply twoSidedCertificate_ext_data
  · simp only [compose]
    rw [restData.1, passEq]
  · simp only [compose, MatrixInverseCertificate.mul]
    rw [restData.2.1, passEq]
  · simp only [compose]
    exact restData.2.2.1
  · simp only [compose]
    rw [restData.2.2.2.1, passEq]
  · simp only [compose, MatrixInverseCertificate.mul]
    rw [restData.2.2.2.2, passEq]

end NormalForms.Research.KannanBachem
