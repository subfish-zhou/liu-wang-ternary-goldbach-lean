import LiuWang.Proof.Campaign20260915.SecondLow.Budget

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.SecondLow

open Interfaces Parameters DirichletZeroCount DirichletZeroCount.Applications
open SourceRoute.SecondArc
open SourceRoute.SecondArc.Continuation
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem actual_M1_original_low_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) * actualM1 N q ≤
      ((32281 : ℝ) / 1000000 + 8 * 0.0000076) / sourceL N := by
  apply (actual_M1_le_original_low_scalar hN hq hseven hnu).trans
  apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
  linarith [originalLowScalar_bound (sourceL_ge_3100 hN)]

#print axioms actual_M1_original_low_paid

end LiuWang.Proof.Campaign20260915.SecondLow
