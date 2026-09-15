import LiuWang.Proof.GlobalZeroDensity.Strip.ExponentialMean
import LiuWang.Proof.GlobalZeroDensity.Strip.CoshWeight

/-! The full-axis mean is obtained from actual finite means, not a pointwise coarse integral. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.Strip

theorem M_critical_polynomial {y : ℝ} (hy : 10000 ≤ y) {T : ℝ} (hT : 0 ≤ T) :
    M y (1 / 2) T ≤ Real.log y * ((91 / 5) * T ^ 2 + (162 / 5) * y * T + 65 * y) := by
  have hy0 : 0 < y := by linarith
  have hl := log_ge_nine hy
  have hu : 0 ≤ T / y := div_nonneg hT hy0.le
  have hbudget := sieved_mean_budget hy hu
  rw [mul_div_cancel₀ _ hy0.ne'] at hbudget
  have hb := (Q_mean_sieved y hT).trans hbudget
  have h := M_critical_le_Q_mean y hT
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (202 / 25) * (2 + T) by positivity)
  have hid : y * Real.log y * ((9 / 4) * (T / y) + 4) =
      Real.log y * ((9 / 4) * T + 4 * y) := by field_simp
  rw [hid] at hh
  have hyl : 202 ≤ (1 / 25) * y * Real.log y := by nlinarith
  have he := mul_le_mul_of_nonneg_right hyl hT
  have htlog : 0 ≤ T * Real.log y := mul_nonneg hT (by linarith)
  have hyt : 10000 * (T * Real.log y) ≤ y * (T * Real.log y) :=
    mul_le_mul_of_nonneg_right hy htlog
  have hylog : 0 ≤ y * Real.log y := by positivity
  have ht2log : 0 ≤ T ^ 2 * Real.log y := by positivity
  nlinarith

theorem critical_mean_moment_integrable {y r : ℝ} (hy : 10000 ≤ y) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => Real.exp (-u / r) / r * M y (1 / 2) u) (Ici 0) := by
  have hm0 := (exp_moment_integrable hr 0).const_mul ((65 * y * Real.log y) / r)
  have hm1 := (exp_moment_integrable hr 1).const_mul (((162 / 5) * y * Real.log y) / r)
  have hm2 := (exp_moment_integrable hr 2).const_mul (((91 / 5) * Real.log y) / r)
  have hmajor : IntegrableOn (fun u : ℝ =>
      Real.exp (-u / r) / r *
        (Real.log y * ((91 / 5) * u ^ 2 + (162 / 5) * y * u + 65 * y))) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    unfold IntegrableOn
    convert (hm2.fun_add hm1).fun_add hm0 using 1
    ext u
    simp only [pow_zero, pow_one]
    ring
  apply hmajor.mono' _ ?_
  · have hc : Continuous (fun u : ℝ => M y (1 / 2) u) := by
      have hv := continuous_vertical_F y (by norm_num : (1 / 2 : ℝ) ≠ 1)
      have hprim : Continuous (fun u : ℝ => ∫ t in (0 : ℝ)..u,
          F y (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) :=
        continuous_iff_continuousAt.mpr (fun u => (hv.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt)
      have he (u : ℝ) : M y (1 / 2) u =
          (∫ t in (0 : ℝ)..u, F y (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) -
          (∫ t in (0 : ℝ)..(-u), F y (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) :=
        (intervalIntegral.integral_interval_sub_left (hv.intervalIntegrable _ _)
          (hv.intervalIntegrable _ _)).symm
      simp_rw [he]
      exact hprim.sub (hprim.comp continuous_id.neg)
    exact ((Real.continuous_exp.comp (continuous_id.neg.div_const r)).div_const r).mul hc
      |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hm := M_integrable_nonneg y (σ := 1 / 2) (by norm_num) hu
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hm.2)]
    exact mul_le_mul_of_nonneg_left (M_critical_polynomial hy hu) (by positivity)

theorem critical_exponential_mean {y : ℝ} (hy : 10000 ≤ y) {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => F y ((1 / 2 : ℂ) + t * Complex.I) * Real.exp (-|t| / r)) ∧
      (∫ t : ℝ, F y ((1 / 2 : ℂ) + t * Complex.I) * Real.exp (-|t| / r)) ≤
        Real.log y * ((182 / 5) * r ^ 2 + (162 / 5) * y * r + 65 * y) := by
  have hc : Continuous (fun t : ℝ => F y ((1 / 2 : ℂ) + t * Complex.I)) := by
    simpa using continuous_vertical_F y (by norm_num : (1 / 2 : ℝ) ≠ 1)
  have hmean : IntegrableOn (fun u : ℝ => Real.exp (-u / r) / r *
      (∫ t in -u..u, F y ((1 / 2 : ℂ) + t * Complex.I))) (Ici 0) := by
    simpa [M] using critical_mean_moment_integrable hy hr
  obtain ⟨hi, he⟩ := exponential_window_identity hc (fun _ => sq_nonneg _) hr hmean
  refine ⟨hi, ?_⟩
  rw [he]
  have hm0 := (exp_moment_integrable hr 0).const_mul ((65 * y * Real.log y) / r)
  have hm1 := (exp_moment_integrable hr 1).const_mul (((162 / 5) * y * Real.log y) / r)
  have hm2 := (exp_moment_integrable hr 2).const_mul (((91 / 5) * Real.log y) / r)
  let p (u : ℝ) := ((91 / 5) * Real.log y / r) * (u ^ 2 * Real.exp (-u / r)) +
    ((162 / 5) * y * Real.log y / r) * (u ^ 1 * Real.exp (-u / r)) +
    (65 * y * Real.log y / r) * (u ^ 0 * Real.exp (-u / r))
  have hp : IntegrableOn p (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr ((hm2.fun_add hm1).fun_add hm0)
  have hb := integral_mono_ae hmean hp ?_
  · have heval : (∫ u in Ici (0 : ℝ), p u) =
        Real.log y * ((182 / 5) * r ^ 2 + (162 / 5) * y * r + 65 * y) := by
      rw [integral_Ici_eq_integral_Ioi]
      dsimp [p]
      rw [integral_add (hm2.fun_add hm1) hm0, integral_add hm2 hm1,
        integral_const_mul, integral_const_mul, integral_const_mul,
        exp_moment_integral hr 2, exp_moment_integral hr 1, exp_moment_integral hr 0]
      norm_num
      field_simp
      ring
    exact hb.trans_eq heval
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have h := mul_le_mul_of_nonneg_left (M_critical_polynomial hy hu)
      (show 0 ≤ Real.exp (-u / r) / r by positivity)
    have heq : p u = Real.exp (-u / r) / r *
        (Real.log y * ((91 / 5) * u ^ 2 + (162 / 5) * y * u + 65 * y)) := by
      dsimp [p]
      ring
    rw [heq]
    simpa only [M, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h

theorem weightedMean_critical_sharp {y : ℝ} (hy : 10000 ≤ y) :
    weightedMean y (1 / 2) ≤ 230 * y ^ 2 * Real.log y := by
  have hy0 : 0 < y := by linarith
  have hl := log_ge_nine hy
  have hr : 0 < (4 / 3) * y := by positivity
  obtain ⟨hi, hb⟩ := critical_exponential_mean hy hr
  have hg := integral_mono (integrable_regularG_critical_sq (by linarith : 1 ≤ y))
    (hi.const_mul (21 / 10)) (fun t => by simpa only [mul_assoc] using regularG_critical_weight hy t)
  rw [integral_const_mul] at hg
  have hbound := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 21 / 10)
  have hys := mul_le_mul_of_nonneg_right hy (show 0 ≤ y * Real.log y by positivity)
  simp only [weightedMean, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  nlinarith

theorem critical_254_13 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    weightedMean y (1 / 2) ≤ (25413 / 100) * y ^ 2 * Real.log y := by
  have hy' : 10000 ≤ y := by linarith [log_six_ge_one]
  have h := weightedMean_critical_sharp hy'
  have hl := log_ge_nine hy'
  nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ Real.log y by linarith)]

end LiuWang.Proof.GlobalZeroDensity.Strip
