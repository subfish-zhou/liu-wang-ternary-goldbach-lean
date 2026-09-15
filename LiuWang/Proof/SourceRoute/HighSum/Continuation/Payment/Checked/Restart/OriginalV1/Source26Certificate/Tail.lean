import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Kernel

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

theorem fourth_exp_bound {L s : ℝ} (hL : 0 ≤ L) (hs : 0 < s) :
    L ^ (4 : ℕ) * Real.exp (-(0.478 / s) * L) ≤ 500 * s ^ (4 : ℕ) := by
  have hp := Real.pow_div_factorial_le_exp ((0.478 : ℝ) * L / s) (by positivity) 4
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hp
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-((0.478 : ℝ) * L / s))).le
  rw [← Real.exp_add, show (239 / 500 : ℝ) * L / s + -(0.478 * L / s) = 0 by ring,
    Real.exp_zero] at hh
  have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hs.le 4)
  field_simp at hm
  rw [show -(L * 0.478 / s) = -(0.478 / s) * L by ring] at hm
  nlinarith [show 0 ≤ L ^ (4 : ℕ) * Real.exp (-(0.478 / s) * L) by positivity,
    pow_nonneg hs.le 4]

theorem integrand_tail_polynomial {L s : ℝ} (hL : 3100 ≤ L) (hs : 100 ≤ s)
    (hsL : s ≤ 18 * Real.log L) :
    integrand L s ≤ 205000000 * s ^ (10 : ℕ) * Real.exp (-s) := by
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < s := by linarith
  have hd : L / 2 ≤ L - 4 * s := by linarith [log_le_original_linear hL]
  have hd0 : 0 < L - 4 * s := by linarith
  have hr : L / (L - 4 * s) ≤ 2 := (div_le_iff₀ hd0).mpr (by linarith)
  have hc : 17102 + 254231 / s ≤ 28000 := by
    have h := (div_le_iff₀ hs0).mpr (show (254231 : ℝ) ≤ 10898 * s by linarith)
    linarith
  have he : Real.exp (1.912 : ℝ) ≤ 7 := exp_1912_upper.trans (by norm_num)
  have hm := mul_le_mul
    (mul_le_mul hc hr (div_nonneg hL0.le hd0.le) (by norm_num)) he
    (Real.exp_pos _).le (by norm_num)
  have hh : (17102 + 254231 / s) * (L / (L - 4 * s)) * Real.exp 1.912 + 16541 ≤ 410000 := by
    linarith
  rw [integrand_factor L hs0.ne']
  calc
    _ ≤ (s ^ (6 : ℕ) * Real.exp (-s) * 410000) * (500 * s ^ (4 : ℕ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hh (by positivity))
        (fourth_exp_bound hL0.le hs0) (by positivity) (by positivity)
    _ = _ := by ring

theorem tail_integral {L b : ℝ} (hL : 3100 ≤ L) (hb : 100 ≤ b)
    (hbL : b ≤ 18 * Real.log L) :
    (∫ s in (100 : ℝ)..b, integrand L s) ≤ 1 / 1000000000000 := by
  have hp (s : ℝ) (hs : 100 ≤ s) :
      s ^ (10 : ℕ) * Real.exp (-s) ≤
        (100 : ℝ) ^ (10 : ℕ) * Real.exp (-10) * Real.exp (-(9 / 10 : ℝ) * s) := by
    have h := power_exp_le 10 (by norm_num : (0 : ℝ) < 100) hs
      (by norm_num : (10 : ℝ) ≤ (1 / 10) * 100)
    have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(9 / 10 : ℝ) * s)).le
    have he : -(1 / 10 : ℝ) * s + -(9 / 10 : ℝ) * s = -s := by ring
    simpa only [mul_assoc, ← Real.exp_add, he, show -(1 / 10 : ℝ) * 100 = -10 by norm_num] using hh
  have hi : IntervalIntegrable (fun s : ℝ =>
      205000000 * 100 ^ (10 : ℕ) * Real.exp (-10) * Real.exp (-(9 / 10 : ℝ) * s))
      volume 100 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := intervalIntegral.integral_mono_on hb
    (integrand_integrable hL (by norm_num) hb hbL) hi (fun s hs =>
      (integrand_tail_polynomial hL hs.1 (hs.2.trans hbL)).trans
        (by simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left (hp s hs.1) (by norm_num : (0 : ℝ) ≤ 205000000))))
  have he :
      (∫ s in (100 : ℝ)..b,
        205000000 * 100 ^ (10 : ℕ) * Real.exp (-10) * Real.exp (-(9 / 10 : ℝ) * s)) ≤
        (205000000 : ℝ) * 100 ^ (10 : ℕ) / (9 / 10) * Real.exp (-100) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : -(9 / 10 : ℝ) ≠ 0),
      integral_exp]
    simp only [smul_eq_mul]
    have hz : -(9 / 10 : ℝ) * 100 = -90 := by norm_num
    rw [hz]
    have hh : 0 ≤ Real.exp (-(9 / 10 : ℝ) * b) := (Real.exp_pos _).le
    have hex : Real.exp (-10) * Real.exp (-90) = Real.exp (-100) := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [mul_nonneg (Real.exp_pos (-10)).le hh]
  have hex : (27 / 10 : ℝ) ^ (100 : ℕ) ≤ Real.exp 100 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
      ((by norm_num : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 100
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  apply (hm.trans he).trans
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos 100)).mpr
  exact (by norm_num : (205000000 : ℝ) * 100 ^ (10 : ℕ) / (9 / 10) ≤
    (1 / 1000000000000 : ℝ) * (27 / 10) ^ (100 : ℕ)).trans
      (mul_le_mul_of_nonneg_left hex (by norm_num))

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
