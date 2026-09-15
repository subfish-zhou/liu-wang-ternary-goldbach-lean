import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.BandDomain

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

theorem low_alpha_envelope_comparison {L : ℝ} (hL : 3100 ≤ L) :
    4 * L ^ (3 : ℕ) * Real.sqrt L * Real.log (10 * Real.pi * L ^ (7 : ℕ)) ≤
      2 * Real.sqrt (10 / Real.pi) * L ^ (3.5 : ℝ) *
        Real.log (10 * Real.pi * L ^ (10 : ℕ)) := by
  have hLp : 0 < L := by linarith
  have hs : (1.7 : ℝ) ≤ Real.sqrt (10 / Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_lt_d2]
  have hl := log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hw0 : 0 ≤ Real.log (10 * Real.pi * L ^ (10 : ℕ)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hc : 0 ≤ Real.log (10 * Real.pi) :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    positivity
  have he : 4 * Real.log (10 * Real.pi * L ^ (7 : ℕ)) ≤
      3.4 * Real.log (10 * Real.pi * L ^ (10 : ℕ)) := by
    simp only [Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by positivity : L ^ (7 : ℕ) ≠ 0),
      Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by positivity : L ^ (10 : ℕ) ≠ 0),
      Real.log_pow, Nat.cast_ofNat]
    linarith [log_ten_pi_le_35]
  have hc := mul_le_mul_of_nonneg_right hs hw0
  have hlog : 4 * Real.log (10 * Real.pi * L ^ (7 : ℕ)) ≤
      2 * Real.sqrt (10 / Real.pi) * Real.log (10 * Real.pi * L ^ (10 : ℕ)) := by
    nlinarith only [he, hc]
  have hm := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ L ^ (3 : ℕ) * Real.sqrt L)
  have hp : L ^ (3.5 : ℝ) = L ^ (3 : ℕ) * Real.sqrt L := by
    rw [show (3.5 : ℝ) = (3 : ℕ) + (1 / 2 : ℝ) by norm_num,
      Real.rpow_add hLp, Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [hp]
  nlinarith only [hm]

theorem actual_low_alpha_normalized {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (Real.sqrt q / q.totient) *
      ((0.001 * (N : ℝ)) ^ (-1 / 2 : ℝ) *
          bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
        ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
          alphaKernel (0.001 * (N : ℝ)) alpha *
            bandMass q alpha (omegaCutoff N q) (middleUpper N q)) ≤
      0.000065 / sourceL N := by
  have hx : 0 < 0.001 * (N : ℝ) := by
    have hn := natCast_pos_of_exp_le hN
    positivity
  let C := 2 * Real.sqrt (10 / Real.pi) * sourceL N ^ (3.5 : ℝ) *
    Real.log (10 * Real.pi * sourceL N ^ (10 : ℕ))
  have hc (alpha : ℝ) (ha : 0 ≤ alpha) :
      (Real.sqrt q / q.totient) *
        bandMass q alpha (omegaCutoff N q) (middleUpper N q) ≤ C :=
    (source_bandMass_bound hN hq ha).trans (low_alpha_envelope_comparison (sourceL_ge_3100 hN))
  have hi := intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 59 / 60)
    ((bandMass_alpha_integrable (q := q) hx (by norm_num)
      (omegaCutoff N q) (middleUpper N q)).const_mul (Real.sqrt q / q.totient))
    (((continuous_alphaKernel hx).intervalIntegrable _ _).mul_const C)
    (by
      intro alpha ha
      have hk : 0 ≤ alphaKernel (0.001 * (N : ℝ)) alpha :=
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (window_base_ge_one hN))
      have hm := mul_le_mul_of_nonneg_left (hc alpha (by linarith [ha.1])) hk
      nlinarith only [hm])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const] at hi
  have hfirst := mul_le_mul_of_nonneg_left (hc (1 / 2) (by norm_num))
    (Real.rpow_nonneg hx.le (-1 / 2 : ℝ))
  have hb := low_alpha_bracket hx
  have hs := original_55_payment (sourceL_ge_3100 hN)
  have hex : Real.exp (sourceL N) * 0.001 = 0.001 * (N : ℝ) := by
    unfold sourceL
    rw [Real.exp_log (natCast_pos_of_exp_le hN)]
    ring
  rw [hex] at hs
  change (0.001 * (N : ℝ)) ^ (-1 / 60 : ℝ) * C ≤ _ at hs
  rw [← hb] at hs
  nlinarith only [hi, hfirst, hs]

theorem actual_low_alpha_strong_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (10 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((0.001 * (N : ℝ)) ^ (-1 / 2 : ℝ) *
          bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
        ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
          alphaKernel (0.001 * (N : ℝ)) alpha *
            bandMass q alpha (omegaCutoff N q) (middleUpper N q)) ≤
      0.00065 * (N : ℝ) / sourceL N := by
  have hh := mul_le_mul_of_nonneg_left (actual_low_alpha_normalized hN hq)
    (by positivity : 0 ≤ 10 * (N : ℝ))
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
