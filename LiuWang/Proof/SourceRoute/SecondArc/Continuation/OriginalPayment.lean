import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ActualIntegral
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.GaussianPayment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation

theorem actual_516_payment_of_source_totient {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hphi : (q : ℝ) / (Nat.totient q : ℝ) ≤ sourceNu (sourceL N ^ (3 : ℕ))) :
    (8 * (N : ℝ) * Real.sqrt q / (Nat.totient q : ℝ)) * actualStripIntegral N q ≤
      0.000021 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hNp := natCast_pos_of_exp_le hN
  have hi := actual_contribution_516_le hN hq
  have he := original_endpoints hL
  have hz : 0 ≤ ∫ z in Real.log (3.36 * sourceL N ^ (3 : ℕ))..
      Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)), originalKernel (sourceL N) z := by
    apply intervalIntegral.integral_nonneg he.2
    intro z hz
    exact originalKernel_nonneg hL (he.1.trans_le hz.1)
  have hb := original_516_scalar_payment hL
  change 112000 * sourceL N * sourceNu (sourceL N ^ (3 : ℕ)) *
    (∫ z in Real.log (3.36 * sourceL N ^ (3 : ℕ))..
      Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)),
      originalKernel (sourceL N) z) ≤ _ at hb
  change (8 * (N : ℝ) * Real.sqrt q / (Nat.totient q : ℝ)) * actualStripIntegral N q ≤
    112000 * (N : ℝ) * ((q : ℝ) / (Nat.totient q : ℝ)) *
      (∫ z in Real.log (3.36 * sourceL N ^ (3 : ℕ))..
        Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)),
        originalKernel (sourceL N) z) at hi
  apply hi.trans
  apply (le_div_iff₀ hLp).mpr
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hphi (by positivity : 0 ≤ 112000 * (N : ℝ))) hz
  have ht := mul_le_mul_of_nonneg_left hb hNp.le
  nlinarith [mul_le_mul_of_nonneg_right hm hLp.le]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation
