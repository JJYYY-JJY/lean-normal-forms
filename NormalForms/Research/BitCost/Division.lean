/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Multiplication

/-!
# Costed Binary Long Division

`PosNum.divMod` is a most-significant-prefix long-division algorithm. At each
input bit it shifts the current remainder, attempts one subtraction of the
divisor, and appends the corresponding quotient bit. This module mirrors that
control flow, returns quotient and remainder from one shared pass, and charges
the binary subtraction and the sign correction required by Euclidean integer
division.
-/

public section

namespace NormalForms.Research.BitCost

namespace Internal

/-- Constructor inspections for subtraction of unsigned binary words. -/
@[expose] public def numSubSteps : Num → Num → Nat
  | .zero, _ => 1
  | _, .zero => 1
  | .pos left, .pos right => 1 + positiveSubSteps left right

/-- Constructor inspections for unsigned binary successor. -/
@[expose] public def numSuccSteps : Num → Nat
  | .zero => 1
  | .pos magnitude => 1 + positiveSuccSteps magnitude

/-- Unsigned subtraction is linear in the two word lengths. -/
public theorem numSubSteps_le (left right : Num) :
    numSubSteps left right ≤
      left.natSize + right.natSize + 1 := by
  cases left with
  | zero =>
      cases right <;> simp [numSubSteps, Num.natSize]
  | pos left =>
      cases right with
      | zero => simp [numSubSteps, Num.natSize]
      | pos right =>
          simp only [numSubSteps, Num.natSize]
          have bound := positiveSubSteps_le left right
          omega

/-- Unsigned successor is linear in the word length. -/
public theorem numSuccSteps_le (word : Num) :
    numSuccSteps word ≤ word.natSize + 1 := by
  cases word with
  | zero => rfl
  | pos magnitude =>
      simp only [numSuccSteps, Num.natSize]
      have bound := positiveSuccSteps_le magnitude
      omega

/-- Shifting an unsigned word left by one grows it by at most one bit. -/
public theorem numBit0_natSize_le (word : Num) :
    (Num.bit0 word).natSize ≤ word.natSize + 1 := by
  cases word with
  | zero => simp [Num.bit0, Num.natSize]
  | pos magnitude =>
      simp only [Num.bit0, Num.natSize, PosNum.natSize,
        Nat.succ_eq_add_one]
      omega

/-- Shifting and appending one grows an unsigned word by at most one bit. -/
public theorem numBit1_natSize_le (word : Num) :
    (Num.bit1 word).natSize ≤ word.natSize + 1 := by
  cases word with
  | zero => simp [Num.bit1, Num.natSize, PosNum.natSize]
  | pos magnitude =>
      simp only [Num.bit1, Num.natSize, PosNum.natSize,
        Nat.succ_eq_add_one]
      omega

/-- Positive binary successor grows a word by at most one bit. -/
public theorem positiveSucc_natSize_le (word : PosNum) :
    word.succ.natSize ≤ word.natSize + 1 := by
  induction word with
  | one => rfl
  | bit0 word _ =>
      simp only [PosNum.succ, PosNum.natSize,
        Nat.succ_eq_add_one]
      omega
  | bit1 word ih =>
      simp only [PosNum.succ, PosNum.natSize,
        Nat.succ_eq_add_one]
      omega

/-- Unsigned successor grows a word by at most one bit. -/
public theorem numSucc_natSize_le (word : Num) :
    word.succ.natSize ≤ word.natSize + 1 := by
  cases word with
  | zero => rfl
  | pos magnitude =>
      simp only [Num.succ, Num.succ', Num.natSize]
      exact positiveSucc_natSize_le magnitude

/-- A positive predecessor never has more bits than its source. -/
public theorem positivePred_natSize_le (word : PosNum) :
    word.pred'.natSize ≤ word.natSize := by
  rw [Num.natSize_to_nat, PosNum.natSize_to_nat]
  apply Nat.size_le_size
  have value := PosNum.to_nat_eq_succ_pred word
  omega

/-- Adding one to a natural number grows its binary length by at most one. -/
public theorem natSize_succ_le (word : Nat) :
    Nat.size (word + 1) ≤ Nat.size word + 1 := by
  apply Nat.size_le.mpr
  have less := Nat.lt_size_self word
  have positive : 0 < 2 ^ Nat.size word :=
    pow_pos (by decide) _
  rw [pow_succ]
  omega

/--
The remainder returned by positive long division has at most as many bits as
the divisor.
-/
public theorem positiveDivMod_remainder_natSize_le
    (divisor numerator : PosNum) :
    (PosNum.divMod divisor numerator).2.natSize ≤
      divisor.natSize := by
  rw [Num.natSize_to_nat, PosNum.natSize_to_nat]
  apply Nat.size_le_size
  have semantics := (PosNum.divMod_to_nat divisor numerator).2
  rw [← semantics]
  exact Nat.le_of_lt
    (Nat.mod_lt (numerator : Nat) (PosNum.cast_pos divisor))

/--
The quotient returned by positive long division cannot have more bits than
the numerator.
-/
public theorem positiveDivMod_quotient_natSize_le
    (divisor numerator : PosNum) :
    (PosNum.divMod divisor numerator).1.natSize ≤
      numerator.natSize := by
  rw [Num.natSize_to_nat, PosNum.natSize_to_nat]
  apply Nat.size_le_size
  have semantics := (PosNum.divMod_to_nat divisor numerator).1
  rw [← semantics]
  exact Nat.div_le_self _ _

/--
Exact modeled work for the recursive `PosNum.divMod` pass. The subtraction
operand is the shifted remainder produced by the preceding prefix.
-/
@[expose] public def positiveDivModSteps
    (divisor : PosNum) : PosNum → Nat
  | .one =>
      1 + numSubSteps 1 (.pos divisor)
  | .bit0 numerator =>
      let previous := PosNum.divMod divisor numerator
      1 + positiveDivModSteps divisor numerator +
        numSubSteps (Num.bit0 previous.2) (.pos divisor)
  | .bit1 numerator =>
      let previous := PosNum.divMod divisor numerator
      1 + positiveDivModSteps divisor numerator +
        numSubSteps (Num.bit1 previous.2) (.pos divisor)

/--
Long division scans each numerator bit and performs at most one subtraction
whose width is bounded by the divisor width.
-/
public theorem positiveDivModSteps_le
    (divisor numerator : PosNum) :
    positiveDivModSteps divisor numerator ≤
      numerator.natSize * (3 + 2 * divisor.natSize) := by
  induction numerator with
  | one =>
      simp only [positiveDivModSteps, PosNum.natSize]
      have subtraction := numSubSteps_le 1 (.pos divisor)
      have oneWidth : (1 : Num).natSize = 1 := rfl
      have divisorWidth :
          (.pos divisor : Num).natSize = divisor.natSize := rfl
      rw [oneWidth, divisorWidth] at subtraction
      have divisorPositive := PosNum.natSize_pos divisor
      omega
  | bit0 numerator ih =>
      simp only [positiveDivModSteps, PosNum.natSize,
        Nat.succ_eq_add_one]
      let previous := PosNum.divMod divisor numerator
      have remainderWidth :
          previous.2.natSize ≤ divisor.natSize := by
        exact positiveDivMod_remainder_natSize_le divisor numerator
      have shiftedWidth :
          (Num.bit0 previous.2).natSize ≤
            divisor.natSize + 1 :=
        (numBit0_natSize_le previous.2).trans
          (Nat.add_le_add_right remainderWidth 1)
      have subtraction :=
        numSubSteps_le (Num.bit0 previous.2) (.pos divisor)
      have divisorWidth :
          (.pos divisor : Num).natSize = divisor.natSize := rfl
      rw [divisorWidth] at subtraction
      have subtraction' :
          numSubSteps (Num.bit0 previous.2) (.pos divisor) ≤
            2 * divisor.natSize + 2 := by
        omega
      calc
        1 + positiveDivModSteps divisor numerator +
              numSubSteps (Num.bit0 previous.2) (.pos divisor) ≤
            numerator.natSize * (3 + 2 * divisor.natSize) +
              (3 + 2 * divisor.natSize) := by
          omega
        _ = (numerator.natSize + 1) *
              (3 + 2 * divisor.natSize) := by ring
  | bit1 numerator ih =>
      simp only [positiveDivModSteps, PosNum.natSize,
        Nat.succ_eq_add_one]
      let previous := PosNum.divMod divisor numerator
      have remainderWidth :
          previous.2.natSize ≤ divisor.natSize := by
        exact positiveDivMod_remainder_natSize_le divisor numerator
      have shiftedWidth :
          (Num.bit1 previous.2).natSize ≤
            divisor.natSize + 1 :=
        (numBit1_natSize_le previous.2).trans
          (Nat.add_le_add_right remainderWidth 1)
      have subtraction :=
        numSubSteps_le (Num.bit1 previous.2) (.pos divisor)
      have divisorWidth :
          (.pos divisor : Num).natSize = divisor.natSize := rfl
      rw [divisorWidth] at subtraction
      have subtraction' :
          numSubSteps (Num.bit1 previous.2) (.pos divisor) ≤
            2 * divisor.natSize + 2 := by
        omega
      calc
        1 + positiveDivModSteps divisor numerator +
              numSubSteps (Num.bit1 previous.2) (.pos divisor) ≤
            numerator.natSize * (3 + 2 * divisor.natSize) +
              (3 + 2 * divisor.natSize) := by
          omega
        _ = (numerator.natSize + 1) *
              (3 + 2 * divisor.natSize) := by ring

/-- One shared unsigned long-division pass, extended to allow zero numerator. -/
@[expose] public def numDivMod (divisor : PosNum) : Num → Num × Num
  | .zero => (0, 0)
  | .pos numerator => PosNum.divMod divisor numerator

/-- Exact modeled work for `numDivMod`. -/
@[expose] public def numDivModSteps (divisor : PosNum) : Num → Nat
  | .zero => 1
  | .pos numerator => 1 + positiveDivModSteps divisor numerator

@[simp] public theorem numDivMod_quotient
    (divisor : PosNum) (numerator : Num) :
    (numDivMod divisor numerator).1 =
      numerator / (.pos divisor : Num) := by
  cases numerator <;> rfl

@[simp] public theorem numDivMod_remainder
    (divisor : PosNum) (numerator : Num) :
    (numDivMod divisor numerator).2 =
      numerator % (.pos divisor : Num) := by
  cases numerator <;> rfl

public theorem numDivModSteps_le
    (divisor : PosNum) (numerator : Num) :
    numDivModSteps divisor numerator ≤
      1 + numerator.natSize * (3 + 2 * divisor.natSize) := by
  cases numerator with
  | zero => simp [numDivModSteps, Num.natSize]
  | pos numerator =>
      simp only [numDivModSteps, Num.natSize]
      exact Nat.add_le_add_left
        (positiveDivModSteps_le divisor numerator) 1

public theorem numDivMod_remainder_natSize_le
    (divisor : PosNum) (numerator : Num) :
    (numDivMod divisor numerator).2.natSize ≤
      divisor.natSize := by
  cases numerator with
  | zero => simp [numDivMod, Num.natSize]
  | pos numerator =>
      exact positiveDivMod_remainder_natSize_le divisor numerator

public theorem numDivMod_quotient_natSize_le
    (divisor : PosNum) (numerator : Num) :
    (numDivMod divisor numerator).1.natSize ≤
      numerator.natSize := by
  cases numerator with
  | zero => simp [numDivMod, Num.natSize]
  | pos numerator =>
      exact positiveDivMod_quotient_natSize_le divisor numerator

/--
Shared quotient/remainder computation with the Euclidean sign convention used
by Lean integers.
-/
@[expose] public def signMagnitudeDivMod :
    SignMagnitude → SignMagnitude → DivModResult
  | .zero, _ =>
      { quotient := 0, remainder := 0 }
  | numerator, .zero =>
      { quotient := 0, remainder := numerator }
  | .pos numerator, .pos divisor =>
      let result := PosNum.divMod divisor numerator
      { quotient := Num.toZNum result.1
        remainder := Num.toZNum result.2 }
  | .pos numerator, .neg divisor =>
      let result := PosNum.divMod divisor numerator
      { quotient := Num.toZNumNeg result.1
        remainder := Num.toZNum result.2 }
  | .neg numerator, .pos divisor =>
      let result := numDivMod divisor numerator.pred'
      { quotient := Num.toZNumNeg result.1.succ
        remainder := (Num.pos divisor).sub' result.2.succ }
  | .neg numerator, .neg divisor =>
      let result := numDivMod divisor numerator.pred'
      { quotient := Num.toZNum result.1.succ
        remainder := (Num.pos divisor).sub' result.2.succ }

/-- Exact modeled work of the shared signed quotient/remainder computation. -/
@[expose] public def signMagnitudeDivModSteps :
    SignMagnitude → SignMagnitude → Nat
  | .zero, _ => 1
  | _, .zero => 1
  | .pos numerator, .pos divisor =>
      1 + positiveDivModSteps divisor numerator
  | .pos numerator, .neg divisor =>
      1 + positiveDivModSteps divisor numerator
  | .neg numerator, .pos divisor =>
      let result := numDivMod divisor numerator.pred'
      1 + positivePredSteps numerator +
        numDivModSteps divisor numerator.pred' +
        numSuccSteps result.1 +
        numSubSteps (.pos divisor) result.2.succ
  | .neg numerator, .neg divisor =>
      let result := numDivMod divisor numerator.pred'
      1 + positivePredSteps numerator +
        numDivModSteps divisor numerator.pred' +
        numSuccSteps result.1 +
        numSubSteps (.pos divisor) result.2.succ

public theorem signMagnitudeDivMod_quotient
    (numerator divisor : SignMagnitude) :
    (signMagnitudeDivMod numerator divisor).quotient =
      numerator / divisor := by
  change (signMagnitudeDivMod numerator divisor).quotient =
    ZNum.div numerator divisor
  cases numerator <;> cases divisor <;>
    simp [signMagnitudeDivMod, numDivMod_quotient, ZNum.div,
      PosNum.div', Num.succ, Num.toZNum, Num.toZNumNeg]

public theorem signMagnitudeDivMod_remainder
    (numerator divisor : SignMagnitude) :
    (signMagnitudeDivMod numerator divisor).remainder =
      numerator % divisor := by
  change (signMagnitudeDivMod numerator divisor).remainder =
    ZNum.mod numerator divisor
  cases numerator with
  | zero => cases divisor <;> rfl
  | pos numerator => cases divisor <;> rfl
  | neg numerator =>
      cases divisor with
      | zero =>
          simp only [signMagnitudeDivMod, ZNum.mod, ZNum.abs,
            Num.succ, Num.sub']
          rw [Num.mod_zero, PosNum.succ'_pred']
      | pos divisor | neg divisor =>
          simp only [signMagnitudeDivMod, numDivMod_remainder,
            ZNum.mod, ZNum.abs]

end Internal

/--
Reference sign-magnitude Euclidean quotient and remainder from one modeled
binary long-division pass.
-/
@[expose] public def divModWithCost
    (numerator divisor : SignMagnitude) : WithCost DivModResult :=
  { value := Internal.signMagnitudeDivMod numerator divisor
    cost := Internal.signMagnitudeDivModSteps numerator divisor }

/-- The quotient agrees with standard integer Euclidean division. -/
@[simp] public theorem divModWithCost_quotient_value
    (numerator divisor : SignMagnitude) :
    (divModWithCost numerator divisor).value.quotient.value =
      numerator.value / divisor.value := by
  rw [divModWithCost, Internal.signMagnitudeDivMod_quotient]
  exact ZNum.div_to_int numerator divisor

/-- The remainder agrees with standard integer Euclidean remainder. -/
@[simp] public theorem divModWithCost_remainder_value
    (numerator divisor : SignMagnitude) :
    (divModWithCost numerator divisor).value.remainder.value =
      numerator.value % divisor.value := by
  rw [divModWithCost, Internal.signMagnitudeDivMod_remainder]
  exact ZNum.mod_to_int numerator divisor

/--
Euclidean quotient length is at most one bit longer than the numerator. The
extra bit accounts for negative floor division.
-/
public theorem divModWithCost_quotient_bitLength_le
    (numerator divisor : SignMagnitude) :
    (divModWithCost numerator divisor).value.quotient.bitLength ≤
      numerator.bitLength + 1 := by
  rw [SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs,
    divModWithCost_quotient_value]
  have quotientMagnitude :
      (numerator.value / divisor.value).natAbs ≤
        numerator.value.natAbs + 1 := by
    rw [Int.natAbs_ediv]
    have divided :
        numerator.value.natAbs / divisor.value.natAbs ≤
          numerator.value.natAbs :=
      Nat.div_le_self _ _
    split <;> omega
  exact (Nat.size_le_size quotientMagnitude).trans
    (Internal.natSize_succ_le numerator.value.natAbs)

/-- A nonzero divisor bounds the Euclidean remainder's bit length. -/
public theorem divModWithCost_remainder_bitLength_le
    (numerator divisor : SignMagnitude)
    (divisor_ne_zero : divisor ≠ 0) :
    (divModWithCost numerator divisor).value.remainder.bitLength ≤
      divisor.bitLength := by
  rw [SignMagnitude.bitLength_eq_natSize_natAbs,
    SignMagnitude.bitLength_eq_natSize_natAbs,
    divModWithCost_remainder_value]
  apply Nat.size_le_size
  have divisorValue_ne_zero : divisor.value ≠ 0 := by
    intro valueZero
    apply divisor_ne_zero
    rw [← SignMagnitude.ofInt_value divisor, valueZero]
    rfl
  exact Nat.le_of_lt (by
    apply Int.ofNat_lt.mp
    rw [Int.natAbs_of_nonneg
      (Int.emod_nonneg numerator.value divisorValue_ne_zero)]
    exact Int.emod_lt numerator.value divisorValue_ne_zero)

/--
The Euclidean remainder strictly decreases the unsigned divisor magnitude.
This is the termination theorem used by the costed extended-gcd loop.
-/
public theorem divModWithCost_remainder_measure_lt
    (numerator divisor : SignMagnitude)
    (divisor_ne_zero : divisor ≠ 0) :
    (divModWithCost numerator divisor).value.remainder.value.natAbs <
      divisor.value.natAbs := by
  rw [divModWithCost_remainder_value]
  have divisorValue_ne_zero : divisor.value ≠ 0 := by
    intro valueZero
    apply divisor_ne_zero
    rw [← SignMagnitude.ofInt_value divisor, valueZero]
    rfl
  apply Int.ofNat_lt.mp
  rw [Int.natAbs_of_nonneg
    (Int.emod_nonneg numerator.value divisorValue_ne_zero)]
  exact Int.emod_lt numerator.value divisorValue_ne_zero

/-- Explicit bit-operation budget for one signed long-division pass. -/
@[expose] public def divModBitOperationBound
    (numerator divisor : SignMagnitude) : Nat :=
  8 +
    numerator.bitLength * (3 + 2 * divisor.bitLength) +
    3 * numerator.bitLength +
    3 * divisor.bitLength

/--
The shared quotient/remainder pass has a bilinear schoolbook bound, plus
linear sign-normalization work.
-/
public theorem divModWithCost_cost_le
    (numerator divisor : SignMagnitude) :
    (divModWithCost numerator divisor).cost ≤
      divModBitOperationBound numerator divisor := by
  cases numerator with
  | zero =>
      cases divisor <;>
        simp [divModWithCost, Internal.signMagnitudeDivModSteps,
          divModBitOperationBound, SignMagnitude.bitLength] <;>
        omega
  | pos numerator =>
      cases divisor with
      | zero =>
          simp [divModWithCost, Internal.signMagnitudeDivModSteps,
            divModBitOperationBound, SignMagnitude.bitLength]
          omega
      | pos divisor | neg divisor =>
          simp only [divModWithCost,
            Internal.signMagnitudeDivModSteps,
            divModBitOperationBound, SignMagnitude.bitLength]
          have bound :=
            Internal.positiveDivModSteps_le divisor numerator
          omega
  | neg numerator =>
      cases divisor with
      | zero =>
          simp [divModWithCost, Internal.signMagnitudeDivModSteps,
            divModBitOperationBound, SignMagnitude.bitLength]
          omega
      | pos divisor | neg divisor =>
          simp only [divModWithCost,
            Internal.signMagnitudeDivModSteps,
            divModBitOperationBound, SignMagnitude.bitLength]
          let result :=
            Internal.numDivMod divisor numerator.pred'
          have predecessorWidth :=
            Internal.positivePred_natSize_le numerator
          have predecessorCost :=
            Internal.positivePredSteps_le numerator
          have divisionCost :=
            Internal.numDivModSteps_le divisor numerator.pred'
          have quotientWidth :
              result.1.natSize ≤ numerator.natSize := by
            exact (Internal.numDivMod_quotient_natSize_le
              divisor numerator.pred').trans predecessorWidth
          have quotientSuccCost :=
            Internal.numSuccSteps_le result.1
          have remainderWidth :
              result.2.natSize ≤ divisor.natSize :=
            Internal.numDivMod_remainder_natSize_le
              divisor numerator.pred'
          have remainderSuccWidth :=
            Internal.numSucc_natSize_le result.2
          have correctionCost :=
            Internal.numSubSteps_le
              (.pos divisor) result.2.succ
          have divisorWidth :
              (.pos divisor : Num).natSize =
                divisor.natSize := rfl
          rw [divisorWidth] at correctionCost
          have correctionCost' :
              Internal.numSubSteps (.pos divisor) result.2.succ ≤
                2 * divisor.natSize + 2 := by
            omega
          have divisionCost' :
              Internal.numDivModSteps divisor numerator.pred' ≤
                1 + numerator.natSize *
                  (3 + 2 * divisor.natSize) := by
            exact divisionCost.trans
              (Nat.add_le_add_left
                (Nat.mul_le_mul_right
                  (3 + 2 * divisor.natSize) predecessorWidth) 1)
          change
            1 + Internal.positivePredSteps numerator +
                Internal.numDivModSteps divisor numerator.pred' +
                Internal.numSuccSteps result.1 +
                Internal.numSubSteps (.pos divisor) result.2.succ ≤
              8 + numerator.natSize *
                  (3 + 2 * divisor.natSize) +
                3 * numerator.natSize +
                3 * divisor.natSize
          omega

end NormalForms.Research.BitCost
