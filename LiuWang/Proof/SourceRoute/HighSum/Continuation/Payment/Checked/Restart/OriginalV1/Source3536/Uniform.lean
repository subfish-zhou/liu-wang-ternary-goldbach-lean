import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Profiles
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.UniformReduction

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem lambdaKernel_core {L s lam : ℝ} (hL : 3100 ≤ L)
    (hs : 0 < s) (hs' : s ≤ 60) (hlam : 0.1 ≤ lam) :
    lambdaKernel L s lam ≤ lambdaKernel 3100 s lam := by
  have hc : 5 ≤ (lam / s) * 3100 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have h := fifth_exp_le (by norm_num : (0 : ℝ) < 3100) hL hc
  have he (x : ℝ) : lambdaKernel x s lam =
      (Real.exp (-s) / s) * (x ^ 5 * Real.exp (-(lam / s) * x)) := by
    unfold lambdaKernel
    rw [show -s - lam * x / s = -s + (-(lam / s) * x) by ring, Real.exp_add]
    ring
  rw [he, he]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem segment_core {L s a b : ℝ} (hL : 3100 ≤ L)
    (hs : 0 < s) (hs' : s ≤ 60) (ha : 0.1 ≤ a) (hab : a ≤ b) :
    L ^ 4 * Real.exp (-s) * lambdaSegment L s a b ≤
      3100 ^ 4 * Real.exp (-s) * lambdaSegment 3100 s a b := by
  rw [normalized_segment_eq, normalized_segment_eq]
  exact intervalIntegral.integral_mono_on hab (lambdaKernel_integrable _ _ _ _)
    (lambdaKernel_integrable _ _ _ _)
    (fun lam hlam => lambdaKernel_core hL hs hs' (ha.trans hlam.1))

theorem lambdaKernel_polynomial {L s lam : ℝ} (hL : 0 ≤ L)
    (hs : 0 < s) (hlam : 0.1 ≤ lam) :
    lambdaKernel L s lam ≤ 12000000 * s ^ 4 * Real.exp (-s) := by
  have ha : 0 ≤ (0.1 : ℝ) * L / s := by positivity
  have hp := Real.pow_div_factorial_le_exp ((0.1 : ℝ) * L / s) ha 5
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hp
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(0.1 : ℝ) * L / s)).le
  rw [← Real.exp_add, show (1 / 10 : ℝ) * L / s + -(0.1 : ℝ) * L / s = 0 by ring,
    Real.exp_zero] at hh
  have hpow : L ^ 5 * Real.exp (-(0.1 : ℝ) * L / s) ≤ 12000000 * s ^ 5 := by
    have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hs.le 5)
    field_simp at hm
    rw [show -(L * 0.1 / s) = -(0.1 : ℝ) * L / s by ring] at hm
    nlinarith
  have hex : Real.exp (-lam * L / s) ≤ Real.exp (-(0.1 : ℝ) * L / s) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using div_le_div_of_nonneg_right
      (neg_le_neg (mul_le_mul_of_nonneg_right hlam hL)) hs.le
  unfold lambdaKernel
  rw [show -s - lam * L / s = -s + (-lam * L / s) by ring, Real.exp_add]
  have hp' := (mul_le_mul_of_nonneg_left hex (pow_nonneg hL 5)).trans hpow
  have hm := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ Real.exp (-s) / s)
  calc
    _ = Real.exp (-s) / s * (L ^ 5 * Real.exp (-lam * L / s)) := by ring
    _ ≤ _ := hm
    _ = _ := by field_simp

theorem segment_polynomial {L s a b : ℝ} (hL : 0 ≤ L)
    (hs : 0 < s) (ha : 0.1 ≤ a) (hab : a ≤ b) :
    L ^ 4 * Real.exp (-s) * lambdaSegment L s a b ≤
      (b - a) * (12000000 * s ^ 4 * Real.exp (-s)) := by
  rw [normalized_segment_eq]
  have hh := intervalIntegral.integral_mono_on hab (lambdaKernel_integrable _ _ _ _)
    intervalIntegrable_const (fun lam hlam => lambdaKernel_polynomial hL hs (ha.trans hlam.1))
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh

theorem profile35_core {L s : ℝ} (hL : 3100 ≤ L) (hs : 0 < s) (hs' : s ≤ 60) :
    integrand profile35 L s ≤ integrand profile35 3100 s := by
  have h1 := segment_core hL hs hs' c1_bounds.2.2
    (show 1 / c1 ≤ 0.3221 by linarith [c1_bounds.2.1])
  have h2 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.3221)
    (by norm_num : (0.3221 : ℝ) ≤ 0.33)
  have h3 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.33)
    (by norm_num : (0.33 : ℝ) ≤ 0.36)
  unfold integrand
  rw [profile35_segments (by linarith) hs, profile35_segments (by norm_num) hs]
  nlinarith

theorem profile36_core {L s : ℝ} (hL : 3100 ≤ L) (hs : 0 < s) (hs' : s ≤ 60) :
    integrand profile36 L s ≤ integrand profile36 3100 s := by
  have h1 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.12)
    (by norm_num : (0.12 : ℝ) ≤ 0.2743)
  have h2 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.2743)
    (by norm_num : (0.2743 : ℝ) ≤ 0.28)
  have h3 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.28)
    (by norm_num : (0.28 : ℝ) ≤ 0.3)
  have h4 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.3)
    (by norm_num : (0.3 : ℝ) ≤ 0.31)
  have h5 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.31)
    (by norm_num : (0.31 : ℝ) ≤ 0.32)
  have h6 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.32)
    (by norm_num : (0.32 : ℝ) ≤ 0.33)
  have h7 := segment_core hL hs hs' (by norm_num : (0.1 : ℝ) ≤ 0.33)
    (by norm_num : (0.33 : ℝ) ≤ 0.36)
  unfold integrand
  rw [profile36_segments (by linarith) hs, profile36_segments (by norm_num) hs]
  nlinarith

theorem profile35_polynomial {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    integrand profile35 L s ≤ 100000000 * s ^ 4 * Real.exp (-s) := by
  have h1 := segment_polynomial hL.le hs c1_bounds.2.2
    (show 1 / c1 ≤ 0.3221 by linarith [c1_bounds.2.1])
  have h2 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.3221)
    (by norm_num : (0.3221 : ℝ) ≤ 0.33)
  have h3 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.33)
    (by norm_num : (0.33 : ℝ) ≤ 0.36)
  have hn : 0 ≤ s ^ 4 * Real.exp (-s) := by positivity
  unfold integrand
  rw [profile35_segments hL hs]
  norm_num [c1] at h1 ⊢
  nlinarith

theorem profile36_polynomial {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    integrand profile36 L s ≤ 100000000 * s ^ 4 * Real.exp (-s) := by
  have h1 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.12)
    (by norm_num : (0.12 : ℝ) ≤ 0.2743)
  have h2 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.2743)
    (by norm_num : (0.2743 : ℝ) ≤ 0.28)
  have h3 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.28)
    (by norm_num : (0.28 : ℝ) ≤ 0.3)
  have h4 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.3)
    (by norm_num : (0.3 : ℝ) ≤ 0.31)
  have h5 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.31)
    (by norm_num : (0.31 : ℝ) ≤ 0.32)
  have h6 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.32)
    (by norm_num : (0.32 : ℝ) ≤ 0.33)
  have h7 := segment_polynomial hL.le hs (by norm_num : (0.1 : ℝ) ≤ 0.33)
    (by norm_num : (0.33 : ℝ) ≤ 0.36)
  have hn : 0 ≤ s ^ 4 * Real.exp (-s) := by positivity
  unfold integrand
  rw [profile36_segments hL hs]
  nlinarith

theorem polynomial_tail60 {b : ℝ} (hb : 60 ≤ b) :
    (∫ s in (60 : ℝ)..b, 100000000 * s ^ 4 * Real.exp (-s)) ≤ 1 / 10000000000 := by
  have hi : IntervalIntegrable (fun s : ℝ => s ^ 4 * Real.exp (-s)) volume 60 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => tailPrimitive_hasDerivAt s) hi
  have hb0 : 0 ≤ b := by linarith
  have ht : tailPrimitive b ≤ 0 := by
    unfold tailPrimitive
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (Real.exp_pos _).le
  have hex : (27 / 10 : ℝ) ^ 60 ≤ Real.exp 60 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
      ((by norm_num : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 60
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hnum : (100000000 : ℝ) * (60 ^ 4 + 4 * 60 ^ 3 + 12 * 60 ^ 2 + 24 * 60 + 24) ≤
      (1 / 10000000000 : ℝ) * (27 / 10) ^ 60 := by norm_num
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [he]
  have hc : -(100000000 : ℝ) * tailPrimitive 60 ≤ 1 / 10000000000 := by
    unfold tailPrimitive
    rw [Real.exp_neg]
    have hh := (div_le_iff₀ (Real.exp_pos 60)).mpr
      (hnum.trans (mul_le_mul_of_nonneg_left hex (by norm_num)))
    simpa only [div_eq_mul_inv, mul_assoc, mul_neg, neg_mul, neg_neg] using hh
  linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
