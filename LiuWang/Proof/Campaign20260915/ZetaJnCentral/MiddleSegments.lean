import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorKernel

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem jn_middle_pointwise (sigma : ℝ) {eta d y : ℝ} {m : ℕ}
    (he : 0 < eta) (hd : 0 < d) (hy : d ≤ |y|) (hye : |y| ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖rsJnIntegrand sigma eta m N y‖ ≤
      rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 29 * y ^ 2) := by
  have hz : ‖(rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)‖ =
      rsSaddleScale * |y| := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos rsSaddleScale_pos,
      rsDescentPoint_distance]
  have hr := rsSaddleRemainder_gaussian_bound sigma (mul_pos rsSaddleScale_pos he)
    (z := (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))
    (by rw [hz]; exact mul_pos rsSaddleScale_pos (hd.trans_le hy))
    (by rw [hz]; nlinarith [rsSaddleScale_pos]) N
  rw [hz, mul_pow, rsSaddleScale_sq, sq_abs] at hr
  rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul]
  apply (mul_le_mul (exterior_gaussian_bound eta m hd hy hm0 hm1) hr
    (norm_nonneg _) (div_nonneg (Real.exp_pos _).le
      (exterior_denominator_pos hd).le)).trans_eq
  rw [Real.exp_add (|sigma - 1| * Real.log (5 / 2))]
  have hx :
      Real.exp (-Real.pi * y ^ 2) * Real.exp (14 / 29 * (2 * Real.pi * y ^ 2)) =
        Real.exp (-Real.pi / 29 * y ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold rsJnOuterConstant
  rw [← hx]
  ring

theorem jn_middle_half (sigma : ℝ) {eta d A e : ℝ} {m : ℕ}
    (he : 0 < eta) (hd : 0 < d) (hAd : d ≤ A) (hAe : A ≤ eta / 2)
    (heps : |e| = 1) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in d..A, rsJnIntegrand sigma eta m N (e * y)‖ ≤
      rsJnOuterConstant sigma d N * (29 / (2 * Real.pi * d)) *
        Real.exp (-Real.pi / 29 * d ^ 2) := by
  have hC := rsJnOuterConstant_pos sigma hd N
  have hb (y : ℝ) (hy : y ∈ Icc d A) :
      ‖rsJnIntegrand sigma eta m N (e * y)‖ ≤
        rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 29 * y ^ 2) := by
    have hn : |e * y| = y := by
      rw [abs_mul, heps, abs_of_nonneg (hd.le.trans hy.1), one_mul]
    have hs : (e * y) ^ 2 = y ^ 2 := by rw [← sq_abs (e * y), hn]
    have h := jn_middle_pointwise sigma he hd (y := e * y)
      (by rw [hn]; exact hy.1) (by rw [hn]; exact hy.2.trans hAe) hm0 hm1 N
    rw [hs] at h
    exact h
  have hi : IntervalIntegrable (fun y : ℝ =>
      rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 29 * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ =>
      rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 29 * y ^ 2))).intervalIntegrable _ _
  calc
    _ ≤ ∫ y : ℝ in d..A, rsJnOuterConstant sigma d N *
        Real.exp (-Real.pi / 29 * y ^ 2) :=
      intervalIntegral.norm_integral_le_of_norm_le hAd
        (Filter.Eventually.of_forall (fun y hy => hb y ⟨hy.1.le, hy.2⟩)) hi
    _ = rsJnOuterConstant sigma d N *
        (∫ y : ℝ in d..A, Real.exp (-Real.pi / 29 * y ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ rsJnOuterConstant sigma d N *
        (Real.exp (-Real.pi / 29 * d ^ 2) / (2 * (Real.pi / 29) * d)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [neg_div] using
          rsGaussian_tail_interval (by positivity : 0 < Real.pi / 29) hd hAd) hC.le
    _ = _ := by ring

theorem jn_middle_integrals (sigma : ℝ) {eta d A : ℝ} {m : ℕ}
    (he : 0 < eta) (hd : 0 < d) (hAd : d ≤ A) (hAe : A ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    IntervalIntegrable (rsJnIntegrand sigma eta m N) volume d A ∧
    IntervalIntegrable (rsJnIntegrand sigma eta m N) volume (-A) (-d) ∧
    ‖∫ y : ℝ in d..A, rsJnIntegrand sigma eta m N y‖ +
      ‖∫ y : ℝ in (-A)..(-d), rsJnIntegrand sigma eta m N y‖ ≤
        rsJnOuterConstant sigma d N * (29 / (Real.pi * d)) *
          Real.exp (-Real.pi / 29 * d ^ 2) := by
  have hcont : ∀ {y : ℝ}, d ≤ |y| → |y| ≤ A →
      ContinuousAt (rsJnIntegrand sigma eta m N) y := fun hy hA =>
    rsJnIntegrand_continuousAt sigma m N he (hd.trans_le hy) (by linarith)
  have hip : IntervalIntegrable (rsJnIntegrand sigma eta m N) volume d A := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le hAd] at hy
    exact (hcont (by rw [abs_of_nonneg (hd.le.trans hy.1)]; exact hy.1)
      (by rw [abs_of_nonneg (hd.le.trans hy.1)]; exact hy.2)).continuousWithinAt
  have hin : IntervalIntegrable (rsJnIntegrand sigma eta m N) volume (-A) (-d) := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le (by linarith : -A ≤ -d)] at hy
    have hy0 : y ≤ 0 := by linarith [hy.2]
    exact (hcont (by rw [abs_of_nonpos hy0]; linarith [hy.2])
      (by rw [abs_of_nonpos hy0]; linarith [hy.1])).continuousWithinAt
  have hp := jn_middle_half sigma he hd hAd hAe (e := 1) (by norm_num) hm0 hm1 N
  have hn := jn_middle_half sigma he hd hAd hAe (e := -1) (by norm_num) hm0 hm1 N
  simp only [one_mul] at hp
  simp only [neg_one_mul, intervalIntegral.integral_comp_neg] at hn
  refine ⟨hip, hin, (add_le_add hp hn).trans_eq ?_⟩
  ring

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
