import LiuWang.Proof.GlobalZeroDensity.LogBoundary

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.GlobalZeroDensity

theorem critical_mean_is_actual (y u : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I) *
        Q y ((1 / 2 : ℂ) + t * Complex.I) - 1‖ ^ 2)
      MeasureTheory.volume (-u) u := by
  simpa only [F, f, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    using intervalIntegrable_F y u (σ := 1 / 2) (by norm_num)

theorem detector_support_and_convergence (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∀ n : ℕ, (n : ℝ) < y → coefficient y n = 0) ∧
      LSeriesHasSum (coefficient y) s (riemannZeta s * Q y s - 1) :=
  ⟨fun _ hn => coefficient_eq_zero_of_lt hn, f_hasSum hs y⟩

theorem weighted_critical_mean_is_actual {y : ℝ} (hy : 1 ≤ y) :
    MeasureTheory.Integrable (fun t : ℝ =>
      ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) MeasureTheory.volume ∧
      weightedMean y (1 / 2) ≤
        (8192 * (⌈y⌉₊ : ℝ) + 64) * y + 4096 * (⌈y⌉₊ : ℝ) * y ^ 3 :=
  ⟨integrable_regularG_critical_sq hy, weightedMean_critical_le hy⟩

theorem detected_zero_has_actual_order (y : ℝ) {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta s = 0) :
    H y s = 0 ∧ analyticOrderAt riemannZeta s ≤ analyticOrderAt (H y) s :=
  ⟨H_eq_zero_of_zeta_eq_zero hz y, analyticOrder_H_ge_zeta y hs⟩

theorem right_log_boundary_paid {y : ℝ} (hy : 5 ≤ y) {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable (fun t : ℝ =>
      Real.log ‖H y ((2 : ℂ) + t * Complex.I)‖) MeasureTheory.volume (-u) u ∧
      (∫ t in -u..u, |Real.log ‖H y ((2 : ℂ) + t * Complex.I)‖|) ≤
        16 * u / (y - 1) ^ 2 :=
  ⟨intervalIntegrable_log_H_two (by linarith) u, abs_log_integral_two_le hy hu⟩

end LiuWang.Proof.GlobalZeroDensity
