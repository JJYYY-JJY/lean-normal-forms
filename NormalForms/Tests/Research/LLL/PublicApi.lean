/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.LLL

set_option linter.privateModule false
set_option linter.hashCommand false

/-! Compilation-only freeze for the independent LLL research facade. -/

open NormalForms.Research.LLL

#check delta
#check eta
#check nearestInteger
#check delta_eq
#check eta_eq
#check delta_gt_quarter
#check delta_lt_one
#check eta_nonnegative
#check eta_lt_one
#check abs_sub_nearestInteger_le

#check dot
#check rationalRow
#check normSq
#check projectionCoefficient
#check gramSchmidtAux
#check gramSchmidtRow
#check gramSchmidtNormSq
#check gramSchmidtCoefficient
#check gramSchmidtAux_of_ge
#check gramSchmidtAux_of_lt
#check gramSchmidtAux_zero
#check dot_zero_left
#check dot_zero_right
#check dot_add_left
#check dot_add_right
#check dot_smul_left
#check dot_smul_right
#check dot_comm

#check toDense
#check ofDense
#check ofDense_toDense
#check toDense_ofDense
#check ofDense_rowAdd
#check ofDense_rowSwap
#check denseLLL
#check exists_leftTransform_of_memLattice
#check exists_mutualLeftTransforms_of_memLattice_iff

#check HasPositiveGramSchmidtLengths
#check IsSizeReduced
#check SatisfiesLovasz
#check IsLLLReduced
#check IsLLLReduced.positive
#check IsLLLReduced.sizeReduced
#check IsLLLReduced.lovasz
#check isLLLReducedB
#check isLLLReducedB_sound

#check FullRowRankWitness
#check FullRowRankWitness.independent
#check rowPrefix
#check FullRankLLLResult
#check FullRankLLLResult.U
#check FullRankLLLResult.U_cert
#check FullRankLLLResult.reducedBasis
#check FullRankLLLResult.equation
#check FullRankLLLResult.reduced
#check LLLResult
#check LLLResult.rank
#check LLLResult.rank_le_rows
#check LLLResult.U
#check LLLResult.U_cert
#check LLLResult.reducedBasis
#check LLLResult.equation
#check LLLResult.reducedPrefix
#check LLLResult.zeroTail
#check ColumnLLLResult
#check ColumnLLLResult.rank
#check ColumnLLLResult.rank_le_columns
#check ColumnLLLResult.V
#check ColumnLLLResult.V_cert
#check ColumnLLLResult.reducedBasis
#check ColumnLLLResult.equation
#check ColumnLLLResult.reducedRows
#check ColumnLLLResult.zeroColumnTail

#check LLLOperationCount
#check LLLOperationCount.sizeReductions
#check LLLOperationCount.swaps
#check LLLOperationCount.gramSchmidtRefreshes
#check LLLOperationCount.total
#check LLLOperationCount.rowOperations
#check FuelledLLLRun
#check FuelledLLLRun.complete
#check FuelledLLLRun.iterations
#check FuelledLLLRun.operations
#check FuelledLLLRun.candidate
#check FuelledLLLRun.certified

#check basisHeight
#check basisBitLength
#check entry_natAbs_le_basisHeight
#check fullRankLLLFuel
#check lllTrackedEventBound
#check lllWorkingBitWidth
#check lllScalarBitOperationCharge
#check lllScalarPositionsPerEvent
#check PrimitiveCost.addition_call_cost_le_charge
#check PrimitiveCost.multiplication_call_cost_le_charge
#check PrimitiveCost.division_call_cost_le_charge
#check LLLOperationCount.bitOperationCost
#check lllKernelBitOperationBound
#check FullRankLLLProfile
#check FullRankLLLProfile.result
#check FullRankLLLProfile.fuel
#check FullRankLLLProfile.fuel_eq
#check FullRankLLLProfile.operations
#check FullRankLLLProfile.operation_bound
#check FullRankLLLProfile.intermediateCoefficientHeight
#check FullRankLLLProfile.result_height_le
#check FullRankLLLProfile.intermediateCoefficientBitLength
#check FullRankLLLProfile.result_bitLength_le
#check FullRankLLLProfile.bitOperationCost
#check FullRankLLLProfile.bitOperationCost_le

#check fullRankLLLProfilePositive
#check fullRankLLLPositive
#check integerLLL
#check integerColumnLLL
