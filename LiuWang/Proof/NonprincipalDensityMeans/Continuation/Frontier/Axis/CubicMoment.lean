import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.FixedWindow
import LiuWang.Proof.GlobalZeroDensity.Strip.ExponentialMean

/-! A cubic envelope paid by exact exponential moments and the existing Fubini identity. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

theorem cubic_moment {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => Real.exp (-u / y) / y * (1 + u / y) ^ 3) (Ici 0) ∧
      (∫ u in Ici (0 : ℝ), Real.exp (-u / y) / y * (1 + u / y) ^ 3) = 16 := by
  have h0 := (exp_moment_integrable hy 0).const_mul (y⁻¹)
  have h1 := (exp_moment_integrable hy 1).const_mul (3 / y ^ 2)
  have h2 := (exp_moment_integrable hy 2).const_mul (3 / y ^ 3)
  have h3 := (exp_moment_integrable hy 3).const_mul (y ^ 4)⁻¹
  have he (u : ℝ) : Real.exp (-u / y) / y * (1 + u / y) ^ 3 =
      y⁻¹ * (u ^ 0 * Real.exp (-u / y)) +
      (3 / y ^ 2) * (u ^ 1 * Real.exp (-u / y)) +
      (3 / y ^ 3) * (u ^ 2 * Real.exp (-u / y)) +
      (y ^ 4)⁻¹ * (u ^ 3 * Real.exp (-u / y)) := by ring
  simp_rw [he]
  constructor
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact ((h0.fun_add h1).fun_add h2).fun_add h3
  · rw [integral_Ici_eq_integral_Ioi, integral_add ((h0.fun_add h1).fun_add h2) h3,
      integral_add (h0.fun_add h1) h2, integral_add h0 h1,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      exp_moment_integral hy 0, exp_moment_integral hy 1,
      exp_moment_integral hy 2, exp_moment_integral hy 3]
    norm_num
    field_simp
    ring

theorem symmetric_window_continuous {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous (fun u : ℝ => ∫ t in -u..u, v t) := by
  have hprim : Continuous (fun u : ℝ => ∫ t in (0 : ℝ)..u, v t) :=
    continuous_iff_continuousAt.mpr
      (fun u => (hv.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt)
  have he (u : ℝ) : (∫ t in -u..u, v t) =
      (∫ t in (0 : ℝ)..u, v t) - (∫ t in (0 : ℝ)..(-u), v t) :=
    (intervalIntegral.integral_interval_sub_left (hv.intervalIntegrable _ _)
      (hv.intervalIntegrable _ _)).symm
  simp_rw [he]
  exact hprim.sub (hprim.comp continuous_id.neg)

theorem exponential_of_cubic_windows {v : ℝ → ℝ} (hv : Continuous v)
    (hv0 : ∀ t, 0 ≤ v t) {y C : ℝ} (hy : 0 < y)
    (hwindow : ∀ u : ℝ, 0 ≤ u → (∫ t in -u..u, v t) ≤ (1 + u / y) ^ 3 * C) :
    Integrable (fun t : ℝ => v t * Real.exp (-|t| / y)) ∧
      (∫ t : ℝ, v t * Real.exp (-|t| / y)) ≤ 16 * C := by
  have hp : IntegrableOn (fun u : ℝ => Real.exp (-u / y) / y *
      ((1 + u / y) ^ 3 * C)) (Ici 0) := by
    simpa only [IntegrableOn, mul_assoc] using (cubic_moment hy).1.mul_const C
  have hc : Continuous (fun u : ℝ => Real.exp (-u / y) / y * (∫ t in -u..u, v t)) :=
    ((Real.continuous_exp.comp (continuous_id.neg.div_const y)).div_const y).mul
      (symmetric_window_continuous hv)
  have hm : IntegrableOn (fun u : ℝ => Real.exp (-u / y) / y * (∫ t in -u..u, v t))
      (Ici 0) := by
    apply hp.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hu0 : 0 ≤ u := hu
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by linarith) (fun t _ => hv0 t)))]
    exact mul_le_mul_of_nonneg_left (hwindow u hu) (by positivity)
  obtain ⟨hi, he⟩ := exponential_window_identity hv hv0 hy hm
  refine ⟨hi, ?_⟩
  rw [he]
  have h := integral_mono_ae hm hp (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact mul_le_mul_of_nonneg_left (hwindow u hu) (by positivity))
  apply h.trans_eq
  simp_rw [← mul_assoc]
  rw [integral_mul_const, (cubic_moment hy).2]

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
