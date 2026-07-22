/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.BitCost

set_option linter.privateModule false
set_option linter.hashCommand false

/-! Compilation-only freeze for the independent bit-cost research facade. -/

open NormalForms.Research.BitCost

#check AcceptanceTier
#check AcceptanceTier.semanticCorrectness
#check AcceptanceTier.ringOperationCount
#check AcceptanceTier.coefficientBitLength
#check AcceptanceTier.bitComplexity
#check SignMagnitude
#check SignMagnitude.value
#check SignMagnitude.ofInt
#check SignMagnitude.bitLength
#check SignMagnitude.magnitude
#check SignMagnitude.value_ofInt
#check SignMagnitude.ofInt_value
#check SignMagnitude.bitLength_eq_natSize_natAbs
#check WithCost
#check WithCost.pure
#check WithCost.map
#check WithCost.bind
#check DivModResult
#check XGCDResult
#check addWithCost
#check addWithCost_value
#check addWithCost_value_bitLength_le
#check addBitOperationBound
#check addWithCost_cost_le
#check mulWithCost
#check mulWithCost_value
#check mulWithCost_value_bitLength_le
#check mulBitOperationBound
#check mulWithCost_cost_le
#check divModWithCost
#check divModWithCost_quotient_value
#check divModWithCost_remainder_value
#check divModWithCost_quotient_bitLength_le
#check divModWithCost_remainder_bitLength_le
#check divModBitOperationBound
#check divModWithCost_cost_le
#check divModWithCost_remainder_measure_lt
#check XGCDSpecification
#check xgcdWithCost
#check xgcdWithCost_spec
#check xgcdWithCost_gcd_value
#check xgcdWithCost_bezout
#check xgcdWithCost_gcd_nonnegative
#check xgcdCoefficientBitBound
#check xgcdWithCost_coefficient_bitLength_le
#check additionCostForBitLengths
#check multiplicationCostForBitLengths
#check xgcdBitOperationBound
#check xgcdWithCost_cost_le
#check SignMagnitude.nonnegative
#check SignMagnitude.restoreCoefficientSign
#check SignMagnitude.nonnegative_value
#check SignMagnitude.nonnegative_bitLength
#check SignMagnitude.restoreCoefficientSign_bitLength
#check SignMagnitude.restoreCoefficientSign_mul_value
#check normalizedXGCDWithCost
#check normalizedXGCDWithCost_spec
#check normalizedXGCDWithCost_gcd_value
#check normalizedXGCDWithCost_bezout
#check normalizedXGCDBitOperationBound
#check normalizedXGCDWithCost_cost_le
#check normalizedXGCDWithCost_coefficient_bitLength_le
#check euclideanIterations
#check euclideanIterations_zero
#check euclideanIterations_succ
#check euclideanIterations_le_productSize
#check euclideanIterations_le_bitLengths
#check boundedXGCDCoefficientHeight
#check boundedEuclideanXGCDWithCost
#check boundedEuclideanXGCDWithCost_spec
#check boundedEuclideanXGCDWithCost_coefficient_natAbs_le
#check boundedXGCDWithCost
#check boundedXGCDWithCost_spec
#check boundedXGCDWithCost_coefficient_natAbs_le
#check divisionCostForBitLengths
#check boundedXGCDCoefficientBitLengthBound
#check boundedXGCDRawCoefficientBitLengthBound
#check boundedEuclideanXGCDWithCost_coefficient_bitLength_le
#check boundedXGCDReductionCostBound
#check boundedXGCDEuclideanUpdateCostBound
#check boundedXGCDStepCostBound
#check boundedEuclideanXGCDDivisions
#check boundedEuclideanXGCDWithCost_cost_le
#check boundedEuclideanXGCDDivisions_eq_euclideanIterations
#check boundedXGCDPolynomialBitOperationBound
#check boundedXGCDWithCost_cost_le
#check boundedXGCDWithCost_cost_le_uniform
