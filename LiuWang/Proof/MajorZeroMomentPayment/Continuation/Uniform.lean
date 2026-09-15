import LiuWang.Proof.MajorZeroMomentPayment.Continuation.LinearTail

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation

theorem integral_norm_core_tail {f : ℝ → ℂ} (hf : Integrable f) {a B C : ℝ}
    (ha : 0 < a) (hb : ∀ eta, ‖f eta‖ ≤ B)
    (hc : ∀ eta, a < |eta| → ‖f eta‖ ≤ C / |eta|^3) :
    (∫ eta : ℝ, ‖f eta‖) ≤ 2 * a * B + C / a^2 := by
  have hg : Integrable (fun eta => (‖f eta‖ : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hf.norm
  have ht := two_sided_tail hg ha (fun eta he => by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hc eta he)
  have hm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -a) (b := a) (C := B) (f := fun eta => (‖f eta‖ : ℂ)) (fun eta _ => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hb eta)
  have h := norm_add_le
    ((∫ eta : ℝ, (‖f eta‖ : ℂ)) - ∫ eta in -a..a, (‖f eta‖ : ℂ))
    (∫ eta in -a..a, (‖f eta‖ : ℂ))
  rw [sub_add_cancel] at h
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun eta => norm_nonneg (f eta)))] at h
  rw [integral_complex_ofReal] at ht
  rw [abs_of_nonneg (by linarith : 0 ≤ a - -a)] at hm
  linarith

theorem finite_norm_le_integral_norm {f : ℝ → ℂ} (hf : Integrable f)
    {delta : ℝ} (hd : 0 ≤ delta) :
    ‖∫ eta in -delta..delta, f eta‖ ≤ ∫ eta : ℝ, ‖f eta‖ := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by linarith : -delta ≤ delta)).trans
  rw [intervalIntegral.integral_of_le (by linarith : -delta ≤ delta)]
  exact setIntegral_le_integral hf.norm (Filter.Eventually.of_forall (fun eta => norm_nonneg (f eta)))

theorem Jrho_real_mass {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1) (eta : ℝ) :
    ‖Jrho N beta eta‖ ≤ (N : ℝ) * realEndpoint N beta := by
  have ha := window_lower_pos hN
  have hbnd (t : ℝ) (ht : t ∈ Icc (sourceWindowLower N) (N : ℝ)) :
      ‖(t : ℂ)^((beta : ℂ) - 1) * charReal (eta * t)‖ ≤ realEndpoint N beta := by
    rw [norm_mul, charReal_norm, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1)]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    have he : sourceWindowLower N = 0.001 * (N : ℝ) := by unfold sourceWindowLower; ring
    exact Real.rpow_le_rpow_of_nonpos (he ▸ ha) (he ▸ ht.1) (by linarith)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := sourceWindowLower N) (b := (N : ℝ)) (C := realEndpoint N beta)
    (f := fun t => (t : ℂ)^((beta : ℂ) - 1) * charReal (eta * t)) (fun t ht => by
      rw [uIoc_of_le (window_lower_le N)] at ht
      exact hbnd t ⟨ht.1.le, ht.2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr (window_lower_le N))] at h
  exact h.trans (by
    have hp : 0 ≤ realEndpoint N beta := by unfold realEndpoint; positivity
    nlinarith [ha.le])

theorem integral_norm_real_triple {N : ℕ} (hN : 0 < N) {r s t : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) :
    (∫ eta : ℝ, ‖tripleKernel N r s t eta‖) ≤
      (3 / Real.pi) * (N : ℝ)^2 *
        (realEndpoint N r * realEndpoint N s * realEndpoint N t) := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have ha : 0 < 1 / (Real.pi * (N : ℝ)) := by positivity
  have hp := integral_norm_core_tail (tripleKernel_integrable hN r s t) ha
    (B := (N : ℝ)^3 * (realEndpoint N r * realEndpoint N s * realEndpoint N t))
    (C := (realEndpoint N r * realEndpoint N s * realEndpoint N t) / Real.pi^3)
    (fun eta => by
      simp only [tripleKernel, norm_mul, charReal_norm, one_mul]
      calc
        _ ≤ ((N : ℝ) * realEndpoint N r) * ((N : ℝ) * realEndpoint N s) *
            ((N : ℝ) * realEndpoint N t) := by
          apply mul_le_mul
            (mul_le_mul (Jrho_real_mass hN hr eta) (Jrho_real_mass hN hs eta)
              (norm_nonneg _) (by unfold realEndpoint; positivity))
            (Jrho_real_mass hN ht eta) (norm_nonneg _) (by unfold realEndpoint; positivity)
        _ = _ := by ring)
    (fun eta he => norm_real_tripleKernel hN hr hs ht (abs_pos.mp (ha.trans he)))
  apply hp.trans_eq
  field_simp
  ring

theorem finite_real_triple_uniform {N : ℕ} (hN : 0 < N) {r s t : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) {delta : ℝ} (hd : 0 ≤ delta) :
    ‖finiteMoment N delta r s t‖ ≤ (3 / Real.pi) * (N : ℝ)^2 *
      (realEndpoint N r * realEndpoint N s * realEndpoint N t) :=
  (finite_norm_le_integral_norm (tripleKernel_integrable hN r s t) hd).trans
    (integral_norm_real_triple hN hr hs ht)

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
