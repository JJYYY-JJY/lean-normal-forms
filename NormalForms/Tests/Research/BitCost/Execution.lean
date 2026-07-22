/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Research.BitCost
meta import all NormalForms.Research.BitCost.Representation
meta import all NormalForms.Research.BitCost.Addition
meta import all NormalForms.Research.BitCost.Multiplication
meta import all NormalForms.Research.BitCost.Division
meta import all NormalForms.Research.BitCost.XGCD
meta import all NormalForms.Research.BitCost.NormalizedXGCD
meta import all NormalForms.Research.BitCost.EuclideanIterations
meta import all NormalForms.Research.BitCost.BoundedXGCD
meta import all NormalForms.Research.BitCost.BoundedXGCDCost

set_option linter.privateModule false
set_option linter.hashCommand false

/-! Executable regressions for the explicit binary reference arithmetic. -/

namespace NormalForms.Tests.Research.BitCost

open NormalForms.Research.BitCost

private def z (value : Int) : SignMagnitude :=
  SignMagnitude.ofInt value

#guard (z (-37)).bitLength = 6
#guard (z 0).bitLength = 0
#guard (z 1).bitLength = 1

#guard (addWithCost (z (-37)) (z 19)).value.value = -18
#guard (addWithCost (z (-37)) (z 19)).cost = 8
#guard (addWithCost (z (-37)) (z 19)).cost ≤
  addBitOperationBound (z (-37)) (z 19)

#guard (mulWithCost (z (-13)) (z 11)).value.value = -143
#guard (mulWithCost (z (-13)) (z 11)).cost = 18
#guard (mulWithCost (z (-13)) (z 11)).cost ≤
  mulBitOperationBound (z (-13)) (z 11)

#guard (divModWithCost (z (-37)) (z 5)).value.quotient.value = -8
#guard (divModWithCost (z (-37)) (z 5)).value.remainder.value = 3
#guard (divModWithCost (z 37) (z (-5))).value.quotient.value = -7
#guard (divModWithCost (z 37) (z (-5))).value.remainder.value = 2
#guard (divModWithCost (z 17) (z 0)).value.quotient.value = 0
#guard (divModWithCost (z 17) (z 0)).value.remainder.value = 17
#guard (divModWithCost (z (-37)) (z 5)).cost ≤
  divModBitOperationBound (z (-37)) (z 5)

private def sampleXGCD := xgcdWithCost (z 240) (z 46)

#guard sampleXGCD.value.gcd.value = 2
#guard sampleXGCD.value.leftCoeff.value = -9
#guard sampleXGCD.value.rightCoeff.value = 47
#guard sampleXGCD.cost = 188
#guard sampleXGCD.cost ≤ xgcdBitOperationBound (z 240) (z 46)
#guard sampleXGCD.value.leftCoeff.bitLength ≤
  xgcdCoefficientBitBound (z 240) (z 46)
#guard sampleXGCD.value.rightCoeff.bitLength ≤
  xgcdCoefficientBitBound (z 240) (z 46)

#guard (xgcdWithCost (z 0) (z 0)).value.gcd.value = 0
#guard (xgcdWithCost (z (-17)) (z 0)).value.gcd.value = 17
#guard (xgcdWithCost (z 17) (z (-5))).value.gcd.value = 1

private def normalizedSignedXGCD :=
  normalizedXGCDWithCost (z 17) (z (-5))

#guard normalizedSignedXGCD.value.gcd.value = 1
#guard normalizedSignedXGCD.value.leftCoeff.value * 17 +
  normalizedSignedXGCD.value.rightCoeff.value * (-5) = 1
#guard normalizedSignedXGCD.cost ≤
  normalizedXGCDBitOperationBound (z 17) (z (-5))
#guard (z (-5)).nonnegative.value = 5
#guard (z (-5)).nonnegative.bitLength = (z (-5)).bitLength
#guard euclideanIterations 240 46 = 5
#guard euclideanIterations 17 5 = 3
#guard euclideanIterations 1 100 = 2
#guard euclideanIterations 240 46 ≤ Nat.size 240 + Nat.size 46 + 1

private def boundedSampleXGCD := boundedXGCDWithCost (z 240) (z 46)
private def boundedSignedXGCD := boundedXGCDWithCost (z 17) (z (-5))

#guard boundedSampleXGCD.value.gcd.value = 2
#guard boundedSampleXGCD.value.leftCoeff.value * 240 +
  boundedSampleXGCD.value.rightCoeff.value * 46 = 2
#guard boundedSignedXGCD.value.leftCoeff.value * 17 +
  boundedSignedXGCD.value.rightCoeff.value * (-5) = 1
#guard boundedSampleXGCD.value.leftCoeff.value.natAbs ≤
  boundedXGCDCoefficientHeight (z 240) (z 46)
#guard boundedSampleXGCD.value.rightCoeff.value.natAbs ≤
  boundedXGCDCoefficientHeight (z 240) (z 46)
#guard boundedEuclideanXGCDDivisions (z 240) (z 46) = 5
#guard boundedXGCDCoefficientBitLengthBound 8 = 20
#guard boundedSampleXGCD.cost ≤
  boundedXGCDPolynomialBitOperationBound (z 240).bitLength (z 46).bitLength

example :
    sampleXGCD.value.leftCoeff.value * 240 +
        sampleXGCD.value.rightCoeff.value * 46 =
      sampleXGCD.value.gcd.value :=
  xgcdWithCost_bezout (z 240) (z 46)

example : 0 ≤ sampleXGCD.value.gcd.value :=
  xgcdWithCost_gcd_nonnegative (z 240) (z 46)

example :
    normalizedSignedXGCD.value.leftCoeff.value * 17 +
        normalizedSignedXGCD.value.rightCoeff.value * (-5) =
      normalizedSignedXGCD.value.gcd.value :=
  normalizedXGCDWithCost_bezout (z 17) (z (-5))

end NormalForms.Tests.Research.BitCost
