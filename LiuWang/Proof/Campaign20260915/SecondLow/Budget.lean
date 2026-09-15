import LiuWang.Proof.Campaign20260915.SecondLow.Cells3

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.Campaign20260915.SecondLow

open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem fixed_rational_budget :
    (∑ i ∈ Finset.range 16, lowFixedCellUpper i) ≤ 0.0000076 := by
  norm_num [Finset.sum_range_succ, low_cell_0, low_cell_1, low_cell_2, low_cell_3,
    low_cell_4, low_cell_5, low_cell_6, low_cell_7, low_cell_8, low_cell_9,
    low_cell_10, low_cell_11, low_cell_12, low_cell_13, low_cell_14, low_cell_15]

theorem originalLowScalar_fixed : originalLowScalar 3100 ≤ 0.0000076 :=
  originalLowScalar_fixed_rational_reduction.trans fixed_rational_budget

theorem originalLowScalar_bound {L : ℝ} (hL : 3100 ≤ L) :
    originalLowScalar L ≤ 0.0000076 :=
  (originalLowScalar_le_base hL).trans originalLowScalar_fixed

#print axioms originalLowScalar_le_base
#print axioms originalLowScalar_fixed
#print axioms originalLowScalar_bound

end LiuWang.Proof.Campaign20260915.SecondLow
