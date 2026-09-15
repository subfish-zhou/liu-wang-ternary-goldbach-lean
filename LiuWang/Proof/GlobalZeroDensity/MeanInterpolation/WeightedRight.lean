import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.RightMean

/-! The actual right full-axis mean has no y loss: an explicit log-fourth bound. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem continuous_M (y : ℝ) {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (fun u : ℝ => M y σ u) := by
  have hv := continuous_vertical_F y hσ
  have hp : Continuous (fun u : ℝ => ∫ t in (0 : ℝ)..u, F y ((σ : ℂ) + t * I)) :=
    continuous_iff_continuousAt.mpr
      (fun u => (hv.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt)
  have he (u : ℝ) : M y σ u =
      (∫ t in (0 : ℝ)..u, F y ((σ : ℂ) + t * I)) -
        (∫ t in (0 : ℝ)..(-u), F y ((σ : ℂ) + t * I)) :=
    (intervalIntegral.integral_interval_sub_left (hv.intervalIntegrable _ _)
      (hv.intervalIntegrable _ _)).symm
  simp_rw [he]
  exact hp.sub (hp.comp continuous_id.neg)

theorem linear_mean_exponential {y σ a b r : ℝ} (hσ : σ ≠ 1) (hr : 0 < r)
    (hb : ∀ T : ℝ, 0 ≤ T → M y σ T ≤ a * T + b) :
    Integrable (fun t : ℝ => F y ((σ : ℂ) + t * I) * Real.exp (-|t| / r)) ∧
      (∫ t : ℝ, F y ((σ : ℂ) + t * I) * Real.exp (-|t| / r)) ≤ a * r + b := by
  let p (u : ℝ) := (a / r) * (u ^ 1 * Real.exp (-u / r)) +
    (b / r) * (u ^ 0 * Real.exp (-u / r))
  have hp1 := (exp_moment_integrable hr 1).const_mul (a / r)
  have hp0 := (exp_moment_integrable hr 0).const_mul (b / r)
  have hp : IntegrableOn p (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (hp1.fun_add hp0)
  have heq (u : ℝ) : p u = Real.exp (-u / r) / r * (a * u + b) := by dsimp [p]; ring
  have hm : IntegrableOn (fun u : ℝ => Real.exp (-u / r) / r * M y σ u) (Ici 0) := by
    apply hp.mono'
      (((Real.continuous_exp.comp (continuous_id.neg.div_const r)).div_const r).mul
        (continuous_M y hσ)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hn := (M_integrable_nonneg y hσ hu).2
    change ‖Real.exp (-u / r) / r * M y σ u‖ ≤ p u
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hn), heq]
    exact mul_le_mul_of_nonneg_left (hb u hu) (by positivity)
  obtain ⟨hi, he⟩ := exponential_window_identity (continuous_vertical_F y hσ)
    (fun _ => sq_nonneg _) hr hm
  refine ⟨hi, ?_⟩
  rw [he]
  have hcomp := integral_mono_ae hm hp ?_
  · have heval : (∫ u in Ici (0 : ℝ), p u) = a * r + b := by
      rw [integral_Ici_eq_integral_Ioi]
      dsimp [p]
      rw [integral_add hp1 hp0, integral_const_mul, integral_const_mul,
        exp_moment_integral hr 1, exp_moment_integral hr 0]
      norm_num
      field_simp
    exact hcomp.trans_eq heval
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hb u hu) (by positivity)

theorem moving_exponential_mean {y r : ℝ} (hy : 10000 ≤ y) (hr : 0 < r) :
    Integrable (fun t : ℝ => F y (((1 + delta y : ℝ) : ℂ) + t * I) *
      Real.exp (-|t| / r)) ∧
    (∫ t : ℝ, F y (((1 + delta y : ℝ) : ℂ) + t * I) * Real.exp (-|t| / r)) ≤
      (6 * r / (y - 1)) * Real.log y ^ 2 + 132 * Real.log y ^ 4 := by
  have hd := delta_bounds hy
  have h := linear_mean_exponential (y := y) (σ := 1 + delta y)
    (a := (6 / (y - 1)) * Real.log y ^ 2) (b := 132 * Real.log y ^ 4)
    (by linarith) hr (fun T hT => by
      have hm := M_moving_sharp hy hT
      convert hm using 1; ring)
  refine ⟨h.1, ?_⟩
  have he : (6 / (y - 1)) * Real.log y ^ 2 * r + 132 * Real.log y ^ 4 =
      (6 * r / (y - 1)) * Real.log y ^ 2 + 132 * Real.log y ^ 4 := by ring
  exact h.2.trans_eq he

theorem weightedMean_moving_sharp {y : ℝ} (hy : 10000 ≤ y) :
    weightedMean y (1 + delta y) ≤ 280 * Real.log y ^ 4 := by
  have hd := delta_bounds hy
  have hL := log_ge_nine hy
  have hy0 : 0 < y := by linarith
  have hr : 0 < (4 / 3) * y := by positivity
  obtain ⟨hi, hb⟩ := moving_exponential_mean hy hr
  have hpoint (t : ℝ) :
      ‖regularG y (((1 + delta y : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
        (21 / 10) * (F y (((1 + delta y : ℝ) : ℂ) + t * I) *
          Real.exp (-|t| / ((4 / 3) * y))) := by
    have hs1 : ((1 + delta y : ℝ) : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, mul_assoc]
      using regularG_weight hy hs1 (by simp; linarith) (by simp; linarith)
  have hg := integral_mono (regularG_right_integrable hy le_rfl (by linarith))
    (hi.const_mul (21 / 10)) hpoint
  rw [integral_const_mul] at hg
  have hratio : 6 * ((4 / 3) * y) / (y - 1) ≤ 16 := by
    apply (div_le_iff₀ (by linarith : 0 < y - 1)).mpr
    linarith
  have hsmall : (21 / 10 : ℝ) * (16 * Real.log y ^ 2 + 132 * Real.log y ^ 4) ≤
      280 * Real.log y ^ 4 := by
    have hL2 : 81 ≤ Real.log y ^ 2 := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ Real.log y ^ 2 - 81 by linarith) (sq_nonneg (Real.log y))]
  have hratio' := mul_le_mul_of_nonneg_right hratio (sq_nonneg (Real.log y))
  have hbound := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 21 / 10)
  change (∫ t : ℝ, ‖regularG y (((1 + delta y : ℝ) : ℂ) + t * I)‖ ^ 2) ≤ _
  linarith

theorem moving_90_5727 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    weightedMean y (1 + delta y) ≤ (905727 / 10000) * Real.log y ^ 5 := by
  have hy' : 10000 ≤ y := by linarith [log_six_ge_one]
  have h := weightedMean_moving_sharp hy'
  have hL := log_ge_nine hy'
  have hc : (280 : ℝ) ≤ (905727 / 10000) * Real.log y := by linarith
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.log y ^ 4 by positivity)
  nlinarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
