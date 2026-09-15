import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelLogLift

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankelDenominator_small_lower {z : ℂ}
    (hz : 2 * Real.pi * ‖z‖ ≤ 1 / 2) :
    Real.pi * ‖z‖ ≤ ‖rsHankelDenominator z‖ := by
  have hn : ‖2 * Real.pi * I * z‖ = 2 * Real.pi * ‖z‖ := by
    simp [Real.norm_eq_abs, Real.pi_pos.le]
  have he := norm_exp_sub_one_sub_id_le (x := 2 * Real.pi * I * z)
    (by rw [hn]; linarith)
  have ht := norm_sub_le (rsHankelDenominator z)
    (rsHankelDenominator z - 2 * Real.pi * I * z)
  rw [sub_sub_cancel, hn] at ht
  change ‖rsHankelDenominator z - 2 * Real.pi * I * z‖ ≤ _ at he
  rw [hn] at he
  have hp : 0 ≤ 2 * Real.pi * ‖z‖ := by positivity
  nlinarith

theorem rsHankelLift_small_bound (s : ℂ) (m : ℕ) {u θ : ℝ}
    (hu : 2 * Real.pi * Real.exp u ≤ 1 / 2)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) :
    ‖rsHankelLift s m (u + θ * I)‖ ≤
      Real.exp (3 * Real.pi / 2 * |s.im| + m) / Real.pi *
        Real.exp ((s.re - 1) * u) := by
  let w : ℂ := u + θ * I
  have hw : ‖exp w‖ = Real.exp u := by simp [w, norm_exp]
  have hq : ‖2 * Real.pi * I * (m : ℂ) * exp w‖ ≤ (m : ℝ) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_I, mul_one, norm_natCast, hw]
    simp only [norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have ha : |θ| ≤ 3 * Real.pi / 2 := abs_le.mpr ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hre : (s * w - 2 * Real.pi * I * m * exp w).re ≤
      s.re * u + (3 * Real.pi / 2 * |s.im| + m) := by
    have hne : -(2 * Real.pi * I * (m : ℂ) * exp w).re ≤ (m : ℝ) :=
      (neg_le_abs _).trans ((abs_re_le_norm _).trans hq)
    have him : -(s.im * θ) ≤ |s.im| * (3 * Real.pi / 2) :=
      (neg_le_abs _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg _))
    have hsre : (s * w).re = s.re * u - s.im * θ := by simp [w, mul_re, mul_im]
    rw [sub_re, hsre]
    linarith
  have hd := rsHankelDenominator_small_lower (z := exp w) (by rwa [hw])
  rw [hw] at hd
  have hdpos : 0 < Real.pi * Real.exp u := mul_pos Real.pi_pos (Real.exp_pos _)
  change ‖exp (s * w - 2 * Real.pi * I * m * exp w) / rsHankelDenominator (exp w)‖ ≤ _
  rw [norm_div, norm_exp]
  calc
    _ ≤ Real.exp (s.re * u + (3 * Real.pi / 2 * |s.im| + m)) /
        (Real.pi * Real.exp u) :=
      div_le_div₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr hre) hdpos hd
    _ = _ := by
      rw [Real.exp_add, show s.re * u = (s.re - 1) * u + u by ring, Real.exp_add]
      field_simp

theorem rsHankelArc_small_bound (s : ℂ) (m : ℕ) {u : ℝ}
    (hu : 2 * Real.pi * Real.exp u ≤ 1 / 2) :
    ‖rsHankelArc s m u‖ ≤
      2 * Real.exp (3 * Real.pi / 2 * |s.im| + m) *
        Real.exp ((s.re - 1) * u) := by
  rw [rsHankelArc, norm_mul, norm_I, one_mul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(Real.pi / 2)) (b := 3 * Real.pi / 2)
    (f := fun θ : ℝ => rsHankelLift s m (u + θ * I))
    (C := Real.exp (3 * Real.pi / 2 * |s.im| + m) / Real.pi *
      Real.exp ((s.re - 1) * u))
    (fun θ hθ => rsHankelLift_small_bound s m hu
      (by simpa [uIcc_of_le (by linarith [Real.pi_pos] :
        -(Real.pi / 2) ≤ 3 * Real.pi / 2)] using uIoc_subset_uIcc hθ))
  convert h using 1
  rw [abs_of_pos (by linarith [Real.pi_pos] :
    0 < 3 * Real.pi / 2 - -(Real.pi / 2))]
  field_simp
  ring

theorem rsHankelArc_tendsto_zero (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (rsHankelArc s m) atBot (𝓝 0) := by
  have hex : Tendsto (fun u : ℝ => Real.exp ((s.re - 1) * u)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (by linarith : 0 < s.re - 1)).mpr tendsto_id)
  have hb := hex.const_mul (2 * Real.exp (3 * Real.pi / 2 * |s.im| + m))
  rw [mul_zero] at hb
  have hsmall : ∀ᶠ u : ℝ in atBot, 2 * Real.pi * Real.exp u ≤ 1 / 2 := by
    have ht := Real.tendsto_exp_atBot.const_mul (2 * Real.pi)
    rw [mul_zero] at ht
    exact ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  exact squeeze_zero_norm' (hsmall.mono (fun u hu => rsHankelArc_small_bound s m hu)) hb

end LiuWang.Proof.Campaign20260915.ZetaValidation
