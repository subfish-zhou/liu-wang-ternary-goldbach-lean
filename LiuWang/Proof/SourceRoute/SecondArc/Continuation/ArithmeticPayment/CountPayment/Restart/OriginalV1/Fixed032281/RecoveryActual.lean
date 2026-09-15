import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryBudget
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Assembly

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

theorem actual_high_alpha_height_032281 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {u : ℝ} (hu : omegaCutoff N q ≤ u) (huv : u ≤ middleUpper N q)
    (hgate : densityGate q ≤ u)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) *
      (∫ y in u..middleUpper N q, heightKernel y *
        ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      ((32281 : ℝ) / 1000000) / sourceL N := by
  exact (actual_high_alpha_height_le_original hN hq hu huv hgate hseven hnu).trans
    (div_le_div_of_nonneg_right (original_all_L_032281 _ (sourceL_ge_3100 hN))
      (by linarith [sourceL_ge_3100 hN]))

theorem actual_high_branch_032281 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) *
      (∫ y in max (omegaCutoff N q) (densityGate q)..middleUpper N q, heightKernel y *
        ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      ((32281 : ℝ) / 1000000) / sourceL N :=
  actual_high_alpha_height_032281 hN hq (le_max_left _ _)
    (max_le (middle_height_domain hN hq).2.1 (densityGate_le_middle hN hq))
    (le_max_right _ _) hseven hnu

#check actual_high_alpha_height_032281
#print axioms actual_high_alpha_height_032281
#check actual_high_branch_032281
#print axioms actual_high_branch_032281

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
