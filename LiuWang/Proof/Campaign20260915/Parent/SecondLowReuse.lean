import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Payment
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.Assembly

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Parent.SecondLowReuse

open Interfaces Parameters DirichletZeroCount DirichletZeroCount.Applications
open SourceRoute.SecondArc SourceRoute.SecondArc.Continuation
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

/-- Reuse the stronger actual low-height estimate, not its coarser scalar envelope. -/
theorem actual_M1_sharp_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) * actualM1 N q ≤
      ((32281 : ℝ) / 1000000 + 8 * 0.000006510372) / sourceL N := by
  by_cases hg : densityGate q ≤ omegaCutoff N q
  · apply (actual_M1_high_only hN hq hg hseven hnu).trans
    apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
    norm_num
  · have hl := mul_le_mul_of_nonneg_left
      (actual_513_normalized_sharp hN hq (le_of_not_ge hg))
      (show (0 : ℝ) ≤ 8 by norm_num)
    have hh := Fixed032281.actual_high_branch_032281 hN hq hseven hnu
    rw [actual_M1_split hN hq, mul_add, actualLowPart, if_neg hg]
    calc
      _ ≤ 8 * (0.000006510372 / sourceL N) +
          ((32281 : ℝ) / 1000000) / sourceL N := by
        apply add_le_add _ hh
        convert hl using 1
        ring
      _ = _ := by ring

/-- The original actual M1 budget is paid without any originalLowScalar premise. -/
theorem actual_M1_original_budget_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) * actualM1 N q ≤
      ((32281 : ℝ) / 1000000 + 8 * 0.0000076) / sourceL N := by
  apply (actual_M1_sharp_paid hN hq hseven hnu).trans
  apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
  norm_num

#print axioms actual_M1_sharp_paid
#print axioms actual_M1_original_budget_paid

end LiuWang.Proof.Campaign20260915.Parent.SecondLowReuse
