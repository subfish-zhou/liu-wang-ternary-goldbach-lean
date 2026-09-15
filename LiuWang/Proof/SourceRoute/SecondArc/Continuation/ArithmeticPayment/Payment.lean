import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.TotientRatio
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ActualIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment

theorem actual_ratio_scalar_payment {q : ℕ} (hq : 0 < q) {L : ℝ}
    (hL : 3100 ≤ L) (hqL : (q : ℝ) ≤ L ^ (3 : ℕ)) :
    112000 * L * ((q : ℝ) / (q.totient : ℝ)) *
      (∫ z in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (10 * Real.pi * L ^ (7 : ℕ)),
        originalKernel L z) ≤ 0.00001777664 := by
  have hs := scaling_bounds hL
  have hratio := totient_ratio_le_scaling hq hL hqL
  have hi := original_integral_le_gaussian hL
  have hz : 0 ≤ ∫ z in Real.log (3.36 * L ^ (3 : ℕ))..
      Real.log (10 * Real.pi * L ^ (7 : ℕ)), originalKernel L z := by
    apply intervalIntegral.integral_nonneg (original_endpoints hL).2
    intro z hz
    exact originalKernel_nonneg hL ((original_endpoints hL).1.trans_le hz.1)
  calc
    _ ≤ (112000 * L * (8 * scaling L ^ 2)) *
        (20 * scaling L * Real.exp (-35.75 * scaling L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hi hz (by positivity)
    _ = (112000 * 3100 * 8 * 20) *
        (scaling L ^ (5 : ℕ) * Real.exp (-35.75 * scaling L)) := by
      nth_rw 1 [hs.2]
      ring
    _ ≤ (112000 * 3100 * 8 * 20) * Real.exp (-35.75 : ℝ) :=
      mul_le_mul_of_nonneg_left (exponential_absorbs_scaling hs.1) (by norm_num)
    _ ≤ (112000 * 3100 * 8 * 20) * 0.00000000000000032 :=
      mul_le_mul_of_nonneg_left fixed_exponential_certificate (by norm_num)
    _ = 0.00001777664 := by norm_num

theorem actual_516_payment_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) * actualStripIntegral N q ≤
      0.00001777664 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hNp := natCast_pos_of_exp_le hN
  have hi := actual_contribution_516_le hN hq
  have hb := actual_ratio_scalar_payment (NeZero.pos q) hL hq
  have ht := mul_le_mul_of_nonneg_left hb hNp.le
  apply hi.trans
  apply (le_div_iff₀ hLp).mpr
  change 112000 * (N : ℝ) * ((q : ℝ) / (q.totient : ℝ)) *
    (∫ z in Real.log (3.36 * sourceL N ^ (3 : ℕ))..
      Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)),
      originalKernel (sourceL N) z) * sourceL N ≤ _
  nlinarith only [ht]

theorem actual_516_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) * actualStripIntegral N q ≤
      0.000021 * (N : ℝ) / sourceL N := by
  apply (actual_516_payment_sharp hN hq).trans
  have hLp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)) hLp.le

theorem strong_kernel_strip_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (5 * (N : ℝ) * Real.sqrt q / q.totient) * actualStripIntegral N q ≤
      0.0000111104 * (N : ℝ) / sourceL N := by
  have h := mul_le_mul_of_nonneg_left (actual_516_payment_sharp hN hq)
    (by norm_num : (0 : ℝ) ≤ 5 / 8)
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment
