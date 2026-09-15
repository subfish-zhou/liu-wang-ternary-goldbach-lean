import LiuWang.Proof.Campaign20260915.SecondTerminal.LastCells7

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem last_fixed_rational_budget :
    lastFixedCoefficient * (∑ i ∈ Finset.range 32, lastFixedCellUpper i) ≤ 0.000024 := by
  norm_num [lastFixedCoefficient, Finset.sum_range_succ,
    last_cell_0, last_cell_1, last_cell_2, last_cell_3, last_cell_4, last_cell_5,
    last_cell_6, last_cell_7, last_cell_8, last_cell_9, last_cell_10, last_cell_11,
    last_cell_12, last_cell_13, last_cell_14, last_cell_15, last_cell_16, last_cell_17,
    last_cell_18, last_cell_19, last_cell_20, last_cell_21, last_cell_22, last_cell_23,
    last_cell_24, last_cell_25, last_cell_26, last_cell_27, last_cell_28, last_cell_29,
    last_cell_30, last_cell_31]

theorem originalLastScalar_fixed :
    originalLastScalar 3100 ≤ 0.000024 :=
  originalLastScalar_fixed_rational_reduction.trans last_fixed_rational_budget

theorem originalLastScalar_payment {L : ℝ} (hL : 3100 ≤ L) :
    originalLastScalar L ≤ 0.000024 :=
  (originalLastScalar_le_base hL).trans originalLastScalar_fixed

theorem actual_last_strip_original_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) *
      (∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
        ∫ alpha in stripUpper q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      0.000024 * (N : ℝ) / sourceL N := by
  have hLp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have h := actual_last_strip_le_fixed_scalar hN hq hnu
  have hp := mul_le_mul_of_nonneg_left originalLastScalar_fixed
    (show 0 ≤ (N : ℝ) / sourceL N by positivity)
  simp only [div_eq_mul_inv] at h hp ⊢
  nlinarith only [h, hp]

#print axioms last_fixed_rational_budget
#print axioms originalLastScalar_payment
#print axioms actual_last_strip_original_payment

end LiuWang.Proof.Campaign20260915.SecondTerminal
