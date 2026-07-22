/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.CoefficientSize
public import NormalForms.Research.BitCost
import all NormalForms.Research.BitCost.BoundedXGCDCost

/-!
# Exact cost mirror for Lean's standard integer XGCD

This module mirrors the `Nat.xgcdAux` path used by the executable integer
Euclidean operations. It records schoolbook binary costs without replacing
the algorithm, proves value equality with the actual `Int.gcdA`/`Int.gcdB`
implementation, and derives explicit coefficient and bit-operation bounds.
-/

public section

namespace NormalForms.Research.ModularHNF

open NormalForms.Research.BitCost

namespace StandardXGCD

def natAuxWithCost :
    (remainder : Nat) →
      Int → Int → Nat → Int → Int →
        WithCost (Nat × Int × Int)
  | 0, _s, _t, previous, previousS, previousT =>
      { value := (previous, previousS, previousT)
        cost := 1 }
  | k + 1, s, t, previous, previousS, previousT =>
      let quotientNat := previous / (k + 1)
      let quotient := SignMagnitude.ofInt quotientNat
      let division := divModWithCost
        (SignMagnitude.ofInt previous) (SignMagnitude.ofInt (k + 1))
      let productS := mulWithCost quotient (SignMagnitude.ofInt s)
      let productT := mulWithCost quotient (SignMagnitude.ofInt t)
      let nextS := addWithCost (SignMagnitude.ofInt previousS) (-productS.value)
      let nextT := addWithCost (SignMagnitude.ofInt previousT) (-productT.value)
      let recursive := natAuxWithCost (previous % (k + 1))
        (previousS - quotientNat * s) (previousT - quotientNat * t)
        (k + 1) s t
      { value := recursive.value
        cost := 1 + division.cost + productS.cost + productT.cost +
          nextS.cost + nextT.cost + recursive.cost }
termination_by remainder _ _ _ _ _ => remainder
decreasing_by
  exact Nat.mod_lt previous (Nat.succ_pos k)

theorem natAuxWithCost_value
    (remainder : Nat) (s t : Int) (previous : Nat)
    (previousS previousT : Int) :
    (natAuxWithCost remainder s t previous previousS previousT).value =
      Nat.xgcdAux remainder s t previous previousS previousT := by
  induction remainder, s, t, previous, previousS, previousT using
      natAuxWithCost.induct with
  | case1 s t previous previousS previousT =>
      simp [natAuxWithCost]
  | case2 k s t previous previousS previousT quotientNat ih =>
      rw [natAuxWithCost, Nat.xgcdAux_rec (Nat.succ_pos k)]
      exact ih

@[simp] theorem natAuxWithCost_initial_value (left right : Nat) :
    (natAuxWithCost left 1 0 right 0 1).value =
      (left.gcd right, left.gcdA right, left.gcdB right) := by
  rw [natAuxWithCost_value, Nat.xgcdAux_val, Nat.xgcd_val]

def natAuxCoefficientBitBound :
    (remainder : Nat) →
      Int → Int → Nat → Int → Int → Nat
  | 0, _s, _t, _previous, previousS, previousT =>
      max (integerBitLength previousS) (integerBitLength previousT)
  | k + 1, s, t, previous, previousS, previousT =>
      let quotientNat := previous / (k + 1)
      let nextS := previousS - quotientNat * s
      let nextT := previousT - quotientNat * t
      max (integerBitLength nextS) <|
        max (integerBitLength nextT) <|
          natAuxCoefficientBitBound (previous % (k + 1))
            nextS nextT (k + 1) s t
termination_by remainder _ _ _ _ _ => remainder
decreasing_by
  exact Nat.mod_lt previous (Nat.succ_pos k)

theorem natAuxWithCost_coefficientBitLength_le
    (remainder : Nat) (s t : Int) (previous : Nat)
    (previousS previousT : Int) :
    integerBitLength
          (natAuxWithCost remainder s t previous previousS previousT).value.2.1 ≤
        natAuxCoefficientBitBound remainder s t previous previousS previousT ∧
      integerBitLength
          (natAuxWithCost remainder s t previous previousS previousT).value.2.2 ≤
        natAuxCoefficientBitBound remainder s t previous previousS previousT := by
  induction remainder, s, t, previous, previousS, previousT using
      natAuxWithCost.induct with
  | case1 s t previous previousS previousT =>
      simp [natAuxWithCost, natAuxCoefficientBitBound]
  | case2 k s t previous previousS previousT quotientNat ih =>
      simp only [natAuxWithCost, natAuxCoefficientBitBound]
      have recursiveBounds :
          integerBitLength
                (natAuxWithCost (previous % (k + 1))
                  (previousS - (previous / (k + 1) : Nat) * s)
                  (previousT - (previous / (k + 1) : Nat) * t)
                  (k + 1) s t).value.2.1 ≤
              natAuxCoefficientBitBound (previous % (k + 1))
                (previousS - (previous / (k + 1) : Nat) * s)
                (previousT - (previous / (k + 1) : Nat) * t)
                (k + 1) s t ∧
            integerBitLength
                (natAuxWithCost (previous % (k + 1))
                  (previousS - (previous / (k + 1) : Nat) * s)
                  (previousT - (previous / (k + 1) : Nat) * t)
                  (k + 1) s t).value.2.2 ≤
              natAuxCoefficientBitBound (previous % (k + 1))
                (previousS - (previous / (k + 1) : Nat) * s)
                (previousT - (previous / (k + 1) : Nat) * t)
                (k + 1) s t := by
        simpa only using ih
      have recursiveLe :
          natAuxCoefficientBitBound (previous % (k + 1))
              (previousS - (previous / (k + 1) : Nat) * s)
              (previousT - (previous / (k + 1) : Nat) * t)
              (k + 1) s t ≤
            max (integerBitLength
                (previousS - (previous / (k + 1) : Nat) * s))
              (max (integerBitLength
                  (previousT - (previous / (k + 1) : Nat) * t))
                (natAuxCoefficientBitBound (previous % (k + 1))
                  (previousS - (previous / (k + 1) : Nat) * s)
                  (previousT - (previous / (k + 1) : Nat) * t)
                  (k + 1) s t)) :=
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
      exact ⟨recursiveBounds.1.trans recursiveLe,
        recursiveBounds.2.trans recursiveLe⟩

theorem natSize_pow_le (base exponent : Nat) :
    Nat.size (base ^ exponent) ≤ exponent * Nat.size base + 1 := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [pow_succ]
      calc
        Nat.size (base ^ exponent * base) ≤
            Nat.size (base ^ exponent) + Nat.size base :=
          NormalForms.Research.BitCost.Internal.natSize_mul_le _ _
        _ ≤ (exponent * Nat.size base + 1) + Nat.size base :=
          Nat.add_le_add_right ih _
        _ = (exponent + 1) * Nat.size base + 1 := by ring

theorem natAuxWithCost_coefficient_natAbs_le
    (remainder : Nat) (s t : Int) (previous : Nat)
    (previousS previousT : Int) (height coefficientHeight : Nat)
    (remainderLe : remainder ≤ height) (previousLe : previous ≤ height)
    (sLe : s.natAbs ≤ coefficientHeight)
    (tLe : t.natAbs ≤ coefficientHeight)
    (previousSLe : previousS.natAbs ≤ coefficientHeight)
    (previousTLe : previousT.natAbs ≤ coefficientHeight) :
    (natAuxWithCost remainder s t previous previousS previousT).value.2.1.natAbs ≤
        coefficientHeight * (height + 1) ^
          euclideanIterations previous remainder ∧
      (natAuxWithCost remainder s t previous previousS previousT).value.2.2.natAbs ≤
        coefficientHeight * (height + 1) ^
          euclideanIterations previous remainder := by
  induction remainder, s, t, previous, previousS, previousT using
      natAuxWithCost.induct generalizing height coefficientHeight with
  | case1 s t previous previousS previousT =>
      simp only [natAuxWithCost, euclideanIterations_zero, pow_zero, mul_one]
      exact ⟨previousSLe, previousTLe⟩
  | case2 k s t previous previousS previousT quotientNat ih =>
      let remainder := k + 1
      let quotient := previous / remainder
      let nextS : Int := previousS - quotient * s
      let nextT : Int := previousT - quotient * t
      let nextCoefficientHeight := coefficientHeight * (height + 1)
      have quotientLe : quotient ≤ height :=
        (Nat.div_le_self previous remainder).trans previousLe
      have quotientNatAbs : (quotient : Int).natAbs = quotient := by simp
      have nextSLe : nextS.natAbs ≤ nextCoefficientHeight := by
        calc
          nextS.natAbs ≤ previousS.natAbs +
              ((quotient : Int) * s).natAbs := Int.natAbs_sub_le _ _
          _ = previousS.natAbs + quotient * s.natAbs := by
            rw [Int.natAbs_mul, quotientNatAbs]
          _ ≤ coefficientHeight + height * coefficientHeight :=
            Nat.add_le_add previousSLe (Nat.mul_le_mul quotientLe sLe)
          _ = nextCoefficientHeight := by
            simp only [nextCoefficientHeight]
            ring
      have nextTLe : nextT.natAbs ≤ nextCoefficientHeight := by
        calc
          nextT.natAbs ≤ previousT.natAbs +
              ((quotient : Int) * t).natAbs := Int.natAbs_sub_le _ _
          _ = previousT.natAbs + quotient * t.natAbs := by
            rw [Int.natAbs_mul, quotientNatAbs]
          _ ≤ coefficientHeight + height * coefficientHeight :=
            Nat.add_le_add previousTLe (Nat.mul_le_mul quotientLe tLe)
          _ = nextCoefficientHeight := by
            simp only [nextCoefficientHeight]
            ring
      have nextRemainderLe : previous % remainder ≤ height :=
        (Nat.le_of_lt (Nat.mod_lt previous (Nat.succ_pos k))).trans remainderLe
      have currentCoefficientLe : coefficientHeight ≤ nextCoefficientHeight := by
        simp only [nextCoefficientHeight]
        have heightPositive : 0 < height + 1 := Nat.succ_pos height
        exact Nat.le_mul_of_pos_right coefficientHeight heightPositive
      have recursive := ih height nextCoefficientHeight nextRemainderLe
        remainderLe nextSLe nextTLe (sLe.trans currentCoefficientLe)
        (tLe.trans currentCoefficientLe)
      have iterationsEq :
          euclideanIterations previous remainder =
            1 + euclideanIterations remainder (previous % remainder) :=
        euclideanIterations_of_pos previous remainder (Nat.succ_pos k)
      have recursive' :
          (natAuxWithCost (previous % (k + 1))
                (previousS - (previous / (k + 1) : Nat) * s)
                (previousT - (previous / (k + 1) : Nat) * t)
                (k + 1) s t).value.2.1.natAbs ≤
              nextCoefficientHeight * (height + 1) ^
                euclideanIterations (k + 1) (previous % (k + 1)) ∧
            (natAuxWithCost (previous % (k + 1))
                (previousS - (previous / (k + 1) : Nat) * s)
                (previousT - (previous / (k + 1) : Nat) * t)
                (k + 1) s t).value.2.2.natAbs ≤
              nextCoefficientHeight * (height + 1) ^
                euclideanIterations (k + 1) (previous % (k + 1)) := by
        simpa only [remainder, quotient, nextS, nextT] using recursive
      simp only [natAuxWithCost]
      rw [iterationsEq]
      constructor
      · exact recursive'.1.trans_eq (by
          simp only [nextCoefficientHeight, remainder]
          ring)
      · exact recursive'.2.trans_eq (by
          simp only [nextCoefficientHeight, remainder]
          ring)

@[expose] def standardIntXGCDUniformCoefficientHeightBound
    (height : Nat) : Nat :=
  (height + 1) ^ (2 * Nat.size height + 1)

@[expose] def standardIntXGCDUniformCoefficientBitBound
    (height : Nat) : Nat :=
  (2 * Nat.size height + 1) * Nat.size (height + 1) + 1

def natAuxBitOperationBound :
    (remainder : Nat) →
      Int → Int → Nat → Int → Int → Nat
  | 0, _s, _t, _previous, _previousS, _previousT => 1
  | k + 1, s, t, previous, previousS, previousT =>
      let quotientNat := previous / (k + 1)
      let quotient := SignMagnitude.ofInt quotientNat
      let previousWord := SignMagnitude.ofInt previous
      let remainderWord := SignMagnitude.ofInt (k + 1)
      let sWord := SignMagnitude.ofInt s
      let tWord := SignMagnitude.ofInt t
      let previousSWord := SignMagnitude.ofInt previousS
      let previousTWord := SignMagnitude.ofInt previousT
      let productS := mulWithCost quotient sWord
      let productT := mulWithCost quotient tWord
      1 + divModBitOperationBound previousWord remainderWord +
        mulBitOperationBound quotient sWord +
        mulBitOperationBound quotient tWord +
        addBitOperationBound previousSWord (-productS.value) +
        addBitOperationBound previousTWord (-productT.value) +
        natAuxBitOperationBound (previous % (k + 1))
          (previousS - quotientNat * s) (previousT - quotientNat * t)
          (k + 1) s t
termination_by remainder _ _ _ _ _ => remainder
decreasing_by
  exact Nat.mod_lt previous (Nat.succ_pos k)

theorem natAuxWithCost_cost_le
    (remainder : Nat) (s t : Int) (previous : Nat)
    (previousS previousT : Int) :
    (natAuxWithCost remainder s t previous previousS previousT).cost ≤
      natAuxBitOperationBound remainder s t previous previousS previousT := by
  induction remainder, s, t, previous, previousS, previousT using
      natAuxWithCost.induct with
  | case1 s t previous previousS previousT =>
      simp [natAuxWithCost, natAuxBitOperationBound]
  | case2 k s t previous previousS previousT quotientNat ih =>
      simp only [natAuxWithCost, natAuxBitOperationBound]
      have recursiveBound :
          (natAuxWithCost (previous % (k + 1))
              (previousS - (previous / (k + 1) : Nat) * s)
              (previousT - (previous / (k + 1) : Nat) * t)
              (k + 1) s t).cost ≤
            natAuxBitOperationBound (previous % (k + 1))
              (previousS - (previous / (k + 1) : Nat) * s)
              (previousT - (previous / (k + 1) : Nat) * t)
              (k + 1) s t := by
        simpa only using ih
      have divisionBound := divModWithCost_cost_le
        (SignMagnitude.ofInt previous) (SignMagnitude.ofInt (k + 1))
      have productSBound := mulWithCost_cost_le
        (SignMagnitude.ofInt (previous / (k + 1) : Nat))
        (SignMagnitude.ofInt s)
      have productTBound := mulWithCost_cost_le
        (SignMagnitude.ofInt (previous / (k + 1) : Nat))
        (SignMagnitude.ofInt t)
      have addSBound := addWithCost_cost_le
        (SignMagnitude.ofInt previousS)
        (-(mulWithCost (SignMagnitude.ofInt (previous / (k + 1) : Nat))
          (SignMagnitude.ofInt s)).value)
      have addTBound := addWithCost_cost_le
        (SignMagnitude.ofInt previousT)
        (-(mulWithCost (SignMagnitude.ofInt (previous / (k + 1) : Nat))
          (SignMagnitude.ofInt t)).value)
      clear ih quotientNat
      omega

@[expose] def standardXGCDAuxStepBitOperationBound
    (height coefficientHeight iterations : Nat) : Nat :=
  let valueBits := Nat.size height
  let coefficientBits :=
    Nat.size (coefficientHeight * (height + 1) ^ iterations)
  1 + divisionCostForBitLengths valueBits valueBits +
    2 * multiplicationCostForBitLengths valueBits coefficientBits +
    2 * additionCostForBitLengths coefficientBits
      (valueBits + coefficientBits)

theorem natAuxWithCost_cost_le_closed
    (remainder : Nat) (s t : Int) (previous : Nat)
    (previousS previousT : Int) (height coefficientHeight : Nat)
    (remainderLe : remainder ≤ height) (previousLe : previous ≤ height)
    (sLe : s.natAbs ≤ coefficientHeight)
    (tLe : t.natAbs ≤ coefficientHeight)
    (previousSLe : previousS.natAbs ≤ coefficientHeight)
    (previousTLe : previousT.natAbs ≤ coefficientHeight) :
    (natAuxWithCost remainder s t previous previousS previousT).cost ≤
      1 + euclideanIterations previous remainder *
        standardXGCDAuxStepBitOperationBound height coefficientHeight
          (euclideanIterations previous remainder) := by
  induction remainder, s, t, previous, previousS, previousT using
      natAuxWithCost.induct generalizing height coefficientHeight with
  | case1 s t previous previousS previousT =>
      simp [natAuxWithCost, euclideanIterations_zero]
  | case2 k s t previous previousS previousT quotientNat ih =>
      let remainder := k + 1
      let quotient := previous / remainder
      let nextS : Int := previousS - quotient * s
      let nextT : Int := previousT - quotient * t
      let nextCoefficientHeight := coefficientHeight * (height + 1)
      let iterations := euclideanIterations previous remainder
      let nextIterations := euclideanIterations remainder (previous % remainder)
      let valueBits := Nat.size height
      let coefficientBits :=
        Nat.size (coefficientHeight * (height + 1) ^ iterations)
      have iterationsEq : iterations = 1 + nextIterations := by
        exact euclideanIterations_of_pos previous remainder (Nat.succ_pos k)
      have quotientLe : quotient ≤ height :=
        (Nat.div_le_self previous remainder).trans previousLe
      have quotientNatAbs : (quotient : Int).natAbs = quotient := by simp
      have nextSLe : nextS.natAbs ≤ nextCoefficientHeight := by
        calc
          nextS.natAbs ≤ previousS.natAbs +
              ((quotient : Int) * s).natAbs := Int.natAbs_sub_le _ _
          _ = previousS.natAbs + quotient * s.natAbs := by
            rw [Int.natAbs_mul, quotientNatAbs]
          _ ≤ coefficientHeight + height * coefficientHeight :=
            Nat.add_le_add previousSLe (Nat.mul_le_mul quotientLe sLe)
          _ = nextCoefficientHeight := by
            simp only [nextCoefficientHeight]
            ring
      have nextTLe : nextT.natAbs ≤ nextCoefficientHeight := by
        calc
          nextT.natAbs ≤ previousT.natAbs +
              ((quotient : Int) * t).natAbs := Int.natAbs_sub_le _ _
          _ = previousT.natAbs + quotient * t.natAbs := by
            rw [Int.natAbs_mul, quotientNatAbs]
          _ ≤ coefficientHeight + height * coefficientHeight :=
            Nat.add_le_add previousTLe (Nat.mul_le_mul quotientLe tLe)
          _ = nextCoefficientHeight := by
            simp only [nextCoefficientHeight]
            ring
      have nextRemainderLe : previous % remainder ≤ height :=
        (Nat.le_of_lt (Nat.mod_lt previous (Nat.succ_pos k))).trans remainderLe
      have currentCoefficientLe : coefficientHeight ≤ nextCoefficientHeight := by
        simp only [nextCoefficientHeight]
        exact Nat.le_mul_of_pos_right coefficientHeight (Nat.succ_pos height)
      have recursiveCost := ih height nextCoefficientHeight nextRemainderLe
        remainderLe nextSLe nextTLe (sLe.trans currentCoefficientLe)
        (tLe.trans currentCoefficientLe)
      have envelopeEq :
          nextCoefficientHeight * (height + 1) ^ nextIterations =
            coefficientHeight * (height + 1) ^ iterations := by
        rw [iterationsEq]
        simp only [nextCoefficientHeight]
        ring
      have stepEq :
          standardXGCDAuxStepBitOperationBound height nextCoefficientHeight
              nextIterations =
            standardXGCDAuxStepBitOperationBound height coefficientHeight
              iterations := by
        unfold standardXGCDAuxStepBitOperationBound
        rw [envelopeEq]
      have recursiveCost' :
          (natAuxWithCost (previous % (k + 1))
              (previousS - (previous / (k + 1) : Nat) * s)
              (previousT - (previous / (k + 1) : Nat) * t)
              (k + 1) s t).cost ≤
            1 + nextIterations *
              standardXGCDAuxStepBitOperationBound height coefficientHeight
                iterations := by
        simpa only [remainder, quotient, nextS, nextT, nextCoefficientHeight,
          nextIterations, stepEq] using recursiveCost
      have coefficientHeightLeEnvelope :
          coefficientHeight ≤
            coefficientHeight * (height + 1) ^ iterations := by
        exact Nat.le_mul_of_pos_right coefficientHeight
          (pow_pos (Nat.succ_pos height) iterations)
      have sBits : Nat.size s.natAbs ≤ coefficientBits :=
        (Nat.size_le_size (sLe.trans coefficientHeightLeEnvelope))
      have tBits : Nat.size t.natAbs ≤ coefficientBits :=
        (Nat.size_le_size (tLe.trans coefficientHeightLeEnvelope))
      have previousSBits : Nat.size previousS.natAbs ≤ coefficientBits :=
        Nat.size_le_size (previousSLe.trans coefficientHeightLeEnvelope)
      have previousTBits : Nat.size previousT.natAbs ≤ coefficientBits :=
        Nat.size_le_size (previousTLe.trans coefficientHeightLeEnvelope)
      have previousBits : Nat.size previous ≤ valueBits :=
        Nat.size_le_size previousLe
      have remainderBits : Nat.size remainder ≤ valueBits :=
        Nat.size_le_size remainderLe
      have quotientBits : Nat.size quotient ≤ valueBits :=
        Nat.size_le_size quotientLe
      let quotientWord := SignMagnitude.ofInt quotient
      let sWord := SignMagnitude.ofInt s
      let tWord := SignMagnitude.ofInt t
      let previousSWord := SignMagnitude.ofInt previousS
      let previousTWord := SignMagnitude.ofInt previousT
      let productS := mulWithCost quotientWord sWord
      let productT := mulWithCost quotientWord tWord
      have quotientWordBits : quotientWord.bitLength ≤ valueBits := by
        simpa [quotientWord,
          SignMagnitude.bitLength_eq_natSize_natAbs] using quotientBits
      have sWordBits : sWord.bitLength ≤ coefficientBits := by
        simpa [sWord, SignMagnitude.bitLength_eq_natSize_natAbs] using sBits
      have tWordBits : tWord.bitLength ≤ coefficientBits := by
        simpa [tWord, SignMagnitude.bitLength_eq_natSize_natAbs] using tBits
      have previousSWordBits : previousSWord.bitLength ≤ coefficientBits := by
        simpa [previousSWord,
          SignMagnitude.bitLength_eq_natSize_natAbs] using previousSBits
      have previousTWordBits : previousTWord.bitLength ≤ coefficientBits := by
        simpa [previousTWord,
          SignMagnitude.bitLength_eq_natSize_natAbs] using previousTBits
      have productSBits : productS.value.bitLength ≤ valueBits + coefficientBits :=
        (mulWithCost_value_bitLength_le quotientWord sWord).trans
          (Nat.add_le_add quotientWordBits sWordBits)
      have productTBits : productT.value.bitLength ≤ valueBits + coefficientBits :=
        (mulWithCost_value_bitLength_le quotientWord tWord).trans
          (Nat.add_le_add quotientWordBits tWordBits)
      have divisionCost :
          (divModWithCost (SignMagnitude.ofInt previous)
              (SignMagnitude.ofInt remainder)).cost ≤
            divisionCostForBitLengths valueBits valueBits :=
        (divModWithCost_cost_le _ _).trans
          (NormalForms.Research.BitCost.Internal.divModBitOperationBound_le_lengths
            _ _ _ _
            (by simpa [SignMagnitude.bitLength_eq_natSize_natAbs] using previousBits)
            (by simpa [SignMagnitude.bitLength_eq_natSize_natAbs] using remainderBits))
      have productSCost : productS.cost ≤
          multiplicationCostForBitLengths valueBits coefficientBits :=
        (mulWithCost_cost_le quotientWord sWord).trans
          (NormalForms.Research.BitCost.Internal.mulBitOperationBound_le_lengths
            _ _ _ _ quotientWordBits sWordBits)
      have productTCost : productT.cost ≤
          multiplicationCostForBitLengths valueBits coefficientBits :=
        (mulWithCost_cost_le quotientWord tWord).trans
          (NormalForms.Research.BitCost.Internal.mulBitOperationBound_le_lengths
            _ _ _ _ quotientWordBits tWordBits)
      have addSCost :
          (addWithCost previousSWord (-productS.value)).cost ≤
            additionCostForBitLengths coefficientBits
              (valueBits + coefficientBits) :=
        (addWithCost_cost_le previousSWord (-productS.value)).trans
          (NormalForms.Research.BitCost.Internal.addBitOperationBound_le_lengths
            _ _ _ _ previousSWordBits (by simpa using productSBits))
      have addTCost :
          (addWithCost previousTWord (-productT.value)).cost ≤
            additionCostForBitLengths coefficientBits
              (valueBits + coefficientBits) :=
        (addWithCost_cost_le previousTWord (-productT.value)).trans
          (NormalForms.Research.BitCost.Internal.addBitOperationBound_le_lengths
            _ _ _ _ previousTWordBits (by simpa using productTBits))
      have localCost :
          1 + (divModWithCost (SignMagnitude.ofInt previous)
                (SignMagnitude.ofInt remainder)).cost +
              productS.cost + productT.cost +
              (addWithCost previousSWord (-productS.value)).cost +
              (addWithCost previousTWord (-productT.value)).cost ≤
              standardXGCDAuxStepBitOperationBound height coefficientHeight
              iterations := by
        change _ ≤
          1 + divisionCostForBitLengths valueBits valueBits +
            2 * multiplicationCostForBitLengths valueBits coefficientBits +
            2 * additionCostForBitLengths coefficientBits
              (valueBits + coefficientBits)
        omega
      have combined :
          1 + (divModWithCost (SignMagnitude.ofInt previous)
                (SignMagnitude.ofInt remainder)).cost +
              productS.cost + productT.cost +
              (addWithCost previousSWord (-productS.value)).cost +
              (addWithCost previousTWord (-productT.value)).cost +
              (natAuxWithCost (previous % remainder) nextS nextT
                remainder s t).cost ≤
            1 + iterations *
              standardXGCDAuxStepBitOperationBound height coefficientHeight
                iterations := by
        calc
          _ ≤ standardXGCDAuxStepBitOperationBound height coefficientHeight
                iterations +
              (natAuxWithCost (previous % remainder) nextS nextT
                remainder s t).cost := Nat.add_le_add_right localCost _
          _ ≤ standardXGCDAuxStepBitOperationBound height coefficientHeight
                iterations +
              (1 + nextIterations *
                standardXGCDAuxStepBitOperationBound height coefficientHeight
                  iterations) := Nat.add_le_add_left recursiveCost' _
          _ = 1 + iterations *
              standardXGCDAuxStepBitOperationBound height coefficientHeight
                iterations := by
            rw [iterationsEq]
            ring
      simpa only [natAuxWithCost, remainder, quotient, nextS, nextT,
        iterations, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        quotientWord, sWord, tWord, previousSWord, previousTWord,
        productS, productT] using combined

def standardIntXGCDWithCost (left right : Int) :
    WithCost (NormalForms.XGCDResult Int) :=
  let auxiliary := natAuxWithCost left.natAbs 1 0 right.natAbs 0 1
  { value :=
      { gcd := auxiliary.value.1
        leftCoeff := if 0 ≤ left then auxiliary.value.2.1
          else -auxiliary.value.2.1
        rightCoeff := if 0 ≤ right then auxiliary.value.2.2
          else -auxiliary.value.2.2 }
    cost := 3 + auxiliary.cost }

theorem standardIntXGCDWithCost_value (left right : Int) :
    (standardIntXGCDWithCost left right).value =
      ComputableEuclideanOps.xgcd left right := by
  rcases left with left | left <;>
    rcases right with right | right <;>
    simp [standardIntXGCDWithCost, natAuxWithCost_initial_value,
      Int.gcdA, Int.gcdB,
      ComputableEuclideanOps.xgcd]

@[expose] def standardIntXGCDCoefficientBitBound
    (left right : Int) : Nat :=
  natAuxCoefficientBitBound left.natAbs 1 0 right.natAbs 0 1

theorem standardIntXGCDWithCost_coefficientBitLength_le (left right : Int) :
    integerBitLength (standardIntXGCDWithCost left right).value.leftCoeff ≤
        standardIntXGCDCoefficientBitBound left right ∧
      integerBitLength (standardIntXGCDWithCost left right).value.rightCoeff ≤
        standardIntXGCDCoefficientBitBound left right := by
  have bounds := natAuxWithCost_coefficientBitLength_le
    left.natAbs 1 0 right.natAbs 0 1
  rcases left with left | left <;>
    rcases right with right | right <;>
    simpa [standardIntXGCDWithCost,
      standardIntXGCDCoefficientBitBound, integerBitLength] using bounds

theorem standardIntXGCDWithCost_coefficient_natAbs_le_uniform
    (left right : Int) (height : Nat)
    (leftLe : left.natAbs ≤ height) (rightLe : right.natAbs ≤ height) :
    (standardIntXGCDWithCost left right).value.leftCoeff.natAbs ≤
        standardIntXGCDUniformCoefficientHeightBound height ∧
      (standardIntXGCDWithCost left right).value.rightCoeff.natAbs ≤
        standardIntXGCDUniformCoefficientHeightBound height := by
  have raw := natAuxWithCost_coefficient_natAbs_le
    left.natAbs 1 0 right.natAbs 0 1 height 1
    leftLe rightLe (by simp) (by simp) (by simp) (by simp)
  have iterations := euclideanIterations_le_bitLengths
    right.natAbs left.natAbs
  have leftBits : Nat.size left.natAbs ≤ Nat.size height :=
    Nat.size_le_size leftLe
  have rightBits : Nat.size right.natAbs ≤ Nat.size height :=
    Nat.size_le_size rightLe
  have iterationBound :
      euclideanIterations right.natAbs left.natAbs ≤
        2 * Nat.size height + 1 := by omega
  have powerBound :
      (height + 1) ^ euclideanIterations right.natAbs left.natAbs ≤
        (height + 1) ^ (2 * Nat.size height + 1) :=
    Nat.pow_le_pow_right (by omega) iterationBound
  rw [one_mul] at raw
  have bounds :
      (natAuxWithCost left.natAbs 1 0 right.natAbs 0 1).value.2.1.natAbs ≤
          (height + 1) ^ (2 * Nat.size height + 1) ∧
        (natAuxWithCost left.natAbs 1 0 right.natAbs 0 1).value.2.2.natAbs ≤
          (height + 1) ^ (2 * Nat.size height + 1) :=
    ⟨raw.1.trans powerBound, raw.2.trans powerBound⟩
  rcases left with left | left <;>
    rcases right with right | right <;>
    simpa [standardIntXGCDWithCost,
      standardIntXGCDUniformCoefficientHeightBound] using bounds

theorem standardIntXGCDWithCost_coefficient_bitLength_le_uniform
    (left right : Int) (height : Nat)
    (leftLe : left.natAbs ≤ height) (rightLe : right.natAbs ≤ height) :
    integerBitLength (standardIntXGCDWithCost left right).value.leftCoeff ≤
        standardIntXGCDUniformCoefficientBitBound height ∧
      integerBitLength (standardIntXGCDWithCost left right).value.rightCoeff ≤
        standardIntXGCDUniformCoefficientBitBound height := by
  have magnitude := standardIntXGCDWithCost_coefficient_natAbs_le_uniform
    left right height leftLe rightLe
  have sizeBound := natSize_pow_le (height + 1)
    (2 * Nat.size height + 1)
  unfold integerBitLength standardIntXGCDUniformCoefficientHeightBound at magnitude
  unfold standardIntXGCDUniformCoefficientBitBound
  exact ⟨(Nat.size_le_size magnitude.1).trans sizeBound,
    (Nat.size_le_size magnitude.2).trans sizeBound⟩

@[expose] def standardIntXGCDBitOperationBound (left right : Int) : Nat :=
  3 + natAuxBitOperationBound left.natAbs 1 0 right.natAbs 0 1

theorem standardIntXGCDWithCost_cost_le (left right : Int) :
    (standardIntXGCDWithCost left right).cost ≤
      standardIntXGCDBitOperationBound left right := by
  unfold standardIntXGCDWithCost standardIntXGCDBitOperationBound
  exact Nat.add_le_add_left
    (natAuxWithCost_cost_le left.natAbs 1 0 right.natAbs 0 1) 3

/-- Closed bit-operation budget for the exact standard integer XGCD path. -/
@[expose] def standardIntXGCDClosedBitOperationBound
    (left right : Int) : Nat :=
  let height := max left.natAbs right.natAbs
  let iterations := euclideanIterations right.natAbs left.natAbs
  4 + iterations *
    standardXGCDAuxStepBitOperationBound height 1 iterations

theorem standardIntXGCDWithCost_cost_le_closed (left right : Int) :
    (standardIntXGCDWithCost left right).cost ≤
      standardIntXGCDClosedBitOperationBound left right := by
  let height := max left.natAbs right.natAbs
  have auxiliaryBound := natAuxWithCost_cost_le_closed
    left.natAbs 1 0 right.natAbs 0 1 height 1
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (by simp) (by simp) (by simp) (by simp)
  simp only [height] at auxiliaryBound
  change 3 + (natAuxWithCost left.natAbs 1 0 right.natAbs 0 1).cost ≤
    4 + euclideanIterations right.natAbs left.natAbs *
      standardXGCDAuxStepBitOperationBound (max left.natAbs right.natAbs) 1
        (euclideanIterations right.natAbs left.natAbs)
  calc
    _ ≤ 3 + (1 + euclideanIterations right.natAbs left.natAbs *
        standardXGCDAuxStepBitOperationBound (max left.natAbs right.natAbs) 1
          (euclideanIterations right.natAbs left.natAbs)) :=
      Nat.add_le_add_left auxiliaryBound 3
    _ = _ := by ring

theorem standardXGCDAuxStepBitOperationBound_mono_iterations
    (height coefficientHeight : Nat) {smaller larger : Nat}
    (le : smaller ≤ larger) :
    standardXGCDAuxStepBitOperationBound height coefficientHeight smaller ≤
      standardXGCDAuxStepBitOperationBound height coefficientHeight larger := by
  have powers :
      coefficientHeight * (height + 1) ^ smaller ≤
        coefficientHeight * (height + 1) ^ larger :=
    Nat.mul_le_mul_left coefficientHeight
      (Nat.pow_le_pow_right (by omega) le)
  let valueBits := Nat.size height
  let smallerBits := Nat.size
    (coefficientHeight * (height + 1) ^ smaller)
  let largerBits := Nat.size
    (coefficientHeight * (height + 1) ^ larger)
  have bitsLe : smallerBits ≤ largerBits := Nat.size_le_size powers
  have multiplicationLe :
      multiplicationCostForBitLengths valueBits smallerBits ≤
        multiplicationCostForBitLengths valueBits largerBits := by
    have baseLe :
        2 * valueBits + smallerBits + 2 ≤
          2 * valueBits + largerBits + 2 := by omega
    have squareLe := Nat.pow_le_pow_left baseLe 2
    have factorLe :
        1 + (2 * valueBits + smallerBits + 2) ^ 2 ≤
          1 + (2 * valueBits + largerBits + 2) ^ 2 :=
      Nat.add_le_add_left squareLe 1
    unfold multiplicationCostForBitLengths
    exact Nat.add_le_add_left (Nat.mul_le_mul bitsLe factorLe) 1
  have additionLe :
      additionCostForBitLengths smallerBits (valueBits + smallerBits) ≤
        additionCostForBitLengths largerBits (valueBits + largerBits) := by
    have baseLe :
        smallerBits + (valueBits + smallerBits) + 1 ≤
          largerBits + (valueBits + largerBits) + 1 := by omega
    have squareLe := Nat.pow_le_pow_left baseLe 2
    unfold additionCostForBitLengths
    omega
  change 1 + divisionCostForBitLengths valueBits valueBits +
        2 * multiplicationCostForBitLengths valueBits smallerBits +
        2 * additionCostForBitLengths smallerBits (valueBits + smallerBits) ≤
      1 + divisionCostForBitLengths valueBits valueBits +
        2 * multiplicationCostForBitLengths valueBits largerBits +
        2 * additionCostForBitLengths largerBits (valueBits + largerBits)
  omega

/-- Operand-height-only bit-operation budget for standard integer XGCD. -/
@[expose] def standardIntXGCDUniformBitOperationBound (height : Nat) : Nat :=
  let iterations := 2 * Nat.size height + 1
  4 + iterations *
    standardXGCDAuxStepBitOperationBound height 1 iterations

theorem standardIntXGCDWithCost_cost_le_uniform
    (left right : Int) (height : Nat)
    (leftLe : left.natAbs ≤ height) (rightLe : right.natAbs ≤ height) :
    (standardIntXGCDWithCost left right).cost ≤
      standardIntXGCDUniformBitOperationBound height := by
  let iterations := euclideanIterations right.natAbs left.natAbs
  let iterationBound := 2 * Nat.size height + 1
  have auxiliaryBound := natAuxWithCost_cost_le_closed
    left.natAbs 1 0 right.natAbs 0 1 height 1 leftLe rightLe
    (by simp) (by simp) (by simp) (by simp)
  have rawIterations := euclideanIterations_le_bitLengths
    right.natAbs left.natAbs
  have leftBits : Nat.size left.natAbs ≤ Nat.size height :=
    Nat.size_le_size leftLe
  have rightBits : Nat.size right.natAbs ≤ Nat.size height :=
    Nat.size_le_size rightLe
  have iterationsLe : iterations ≤ iterationBound := by
    simp only [iterations, iterationBound]
    omega
  have stepLe := standardXGCDAuxStepBitOperationBound_mono_iterations
    height 1 iterationsLe
  have productLe :
      iterations * standardXGCDAuxStepBitOperationBound height 1 iterations ≤
        iterationBound *
          standardXGCDAuxStepBitOperationBound height 1 iterationBound :=
    Nat.mul_le_mul iterationsLe stepLe
  change 3 + (natAuxWithCost left.natAbs 1 0 right.natAbs 0 1).cost ≤ _
  unfold standardIntXGCDUniformBitOperationBound
  change _ ≤ 4 + iterationBound *
    standardXGCDAuxStepBitOperationBound height 1 iterationBound
  calc
    _ ≤ 3 + (1 + iterations *
        standardXGCDAuxStepBitOperationBound height 1 iterations) :=
      Nat.add_le_add_left auxiliaryBound 3
    _ = 4 + iterations *
        standardXGCDAuxStepBitOperationBound height 1 iterations := by ring
    _ ≤ 4 + iterationBound *
        standardXGCDAuxStepBitOperationBound height 1 iterationBound :=
      Nat.add_le_add_left productLe 4

end StandardXGCD

end NormalForms.Research.ModularHNF
