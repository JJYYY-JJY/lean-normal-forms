/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.BitCost

set_option linter.privateModule false
set_option linter.hashCommand false

/-!
# Bit-cost 0.1.0 public API snapshot

Compilation-only freeze for the 49-name research/bit-cost 0.1.0 surface.
The independently checked current additive surface lives in `PublicApi`.
-/

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
