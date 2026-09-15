import LiuWang.Proof.SingularIntegral.Decay
import Mathlib.Topology.Algebra.Indicator

/-!
# 原窗卷积的连续性与点态反演

平移后的两个原窗端点是零测集。支配收敛只用于时域卷积，
Fourier 卷积公式只用于已经证明为 `L¹` 的时域函数。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set FourierTransform
open scoped Interval Topology Convolution
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SingularIntegral

theorem windowWeight_bounded {N : ℕ} (hN : 0 < N) (rho : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖windowWeight N rho t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (cpow_continuousOn_window hN (rho - 1)).norm
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (sourceWindowLower N) (N : ℝ)
  · simp only [windowWeight, indicator_of_mem ht]
    exact (hC (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  · simp [windowWeight, ht]

theorem windowWeight_continuousAt {N : ℕ} (hN : 0 < N) (rho : ℂ) {t : ℝ}
    (ha : t ≠ sourceWindowLower N) (hb : t ≠ N) :
    ContinuousAt (windowWeight N rho) t := by
  apply ((cpow_continuousOn_window hN (rho - 1)).mono interior_subset).continuousAt_indicator
  rw [frontier_Icc (window_lower_le N)]
  simpa using And.intro ha hb

theorem convolution_window_continuous {N : ℕ} (hN : 0 < N) (rho : ℂ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (f ⋆[ContinuousLinearMap.mul ℂ ℂ] windowWeight N rho) := by
  obtain ⟨C, hC, hbound⟩ := windowWeight_bounded hN rho
  apply continuous_iff_continuousAt.2
  intro x
  change ContinuousAt (fun x => ∫ t, f t * windowWeight N rho (x - t)) x
  refine continuousAt_of_dominated
    (bound := fun t => ‖f t‖ * C) ?_ ?_ (hf.norm.mul_const C) ?_
  · exact Filter.Eventually.of_forall fun y =>
      hf.aestronglyMeasurable.mul
        ((windowWeight_stronglyMeasurable N rho).comp_measurable
          (measurable_const.sub measurable_id)).aestronglyMeasurable
  · filter_upwards with y
    filter_upwards with t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
  · filter_upwards [volume.ae_ne (x - sourceWindowLower N), volume.ae_ne (x - (N : ℝ))]
      with t ha hb
    have hw := windowWeight_continuousAt hN rho
      (t := x - t) (by contrapose! ha; linarith) (by contrapose! hb; linarith)
    exact continuousAt_const.mul (hw.comp (f := fun y : ℝ => y - t) (by fun_prop))

theorem convolution_window_bounded {N : ℕ} (hN : 0 < N) (rho : ℂ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    BddAbove (range fun x => ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] windowWeight N rho) x‖) := by
  obtain ⟨C, hC, hbound⟩ := windowWeight_bounded hN rho
  refine ⟨(∫ t, ‖f t‖) * C, ?_⟩
  rintro _ ⟨x, rfl⟩
  change ‖∫ t, f t * windowWeight N rho (x - t)‖ ≤ _
  have h := norm_integral_le_of_norm_le (hf.norm.mul_const C)
    (Filter.Eventually.of_forall fun t => show
      ‖f t * windowWeight N rho (x - t)‖ ≤ ‖f t‖ * C by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
  simpa only [integral_mul_const] using h

def tripleConvolution (N : ℕ) (rho₁ rho₂ rho₃ : ℂ) : ℝ → ℂ :=
  windowWeight N rho₁ ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (windowWeight N rho₂ ⋆[ContinuousLinearMap.mul ℂ ℂ] windowWeight N rho₃)

theorem tripleConvolution_integrable {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    Integrable (tripleConvolution N rho₁ rho₂ rho₃) :=
  (windowWeight_integrable hN rho₁).integrable_convolution _
    ((windowWeight_integrable hN rho₂).integrable_convolution _ (windowWeight_integrable hN rho₃))

theorem tripleConvolution_continuous {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    Continuous (tripleConvolution N rho₁ rho₂ rho₃) :=
  (convolution_window_bounded hN rho₃ (windowWeight_integrable hN rho₂)
    ).continuous_convolution_right_of_integrable _
    (windowWeight_integrable hN rho₁)
    (convolution_window_continuous hN rho₃ (windowWeight_integrable hN rho₂))

theorem fourier_tripleConvolution {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) (eta : ℝ) :
    𝓕 (tripleConvolution N rho₁ rho₂ rho₃) eta =
      Jrho N rho₁ (-eta) * Jrho N rho₂ (-eta) * Jrho N rho₃ (-eta) := by
  simp only [tripleConvolution, Real.fourier_mul_convolution_eq
    (windowWeight_integrable hN rho₁)
    ((windowWeight_integrable hN rho₂).integrable_convolution _ (windowWeight_integrable hN rho₃)),
    Real.fourier_mul_convolution_eq (windowWeight_integrable hN rho₂)
      (windowWeight_integrable hN rho₃),
    Jrho_eq_fourier_neg, neg_neg, mul_assoc]

theorem Jrho_product_integrable {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    Integrable (fun eta : ℝ => Jrho N rho₁ eta * Jrho N rho₂ eta * Jrho N rho₃ eta) := by
  refine (Jrho_triple_integrable hN rho₁ rho₂ rho₃).mono
    (((Jrho_continuous hN rho₁).mul (Jrho_continuous hN rho₂)).mul
      (Jrho_continuous hN rho₃)).aestronglyMeasurable ?_
  filter_upwards with eta
  simp only [norm_mul, charReal_norm, one_mul, le_refl]

theorem fourier_tripleConvolution_integrable {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    Integrable (𝓕 (tripleConvolution N rho₁ rho₂ rho₃)) := by
  have h := (Jrho_product_integrable hN rho₁ rho₂ rho₃).comp_neg
  convert h using 1
  ext eta
  exact fourier_tripleConvolution hN rho₁ rho₂ rho₃ eta

theorem integral_Jrho_triple_eq_convolution {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    (∫ eta : ℝ, charReal (-(N : ℝ) * eta) *
      Jrho N rho₁ eta * Jrho N rho₂ eta * Jrho N rho₃ eta) =
      tripleConvolution N rho₁ rho₂ rho₃ N := by
  have hi := (tripleConvolution_integrable hN rho₁ rho₂ rho₃).fourierInv_fourier_eq
    (v := (N : ℝ))
    (fourier_tripleConvolution_integrable hN rho₁ rho₂ rho₃)
    (tripleConvolution_continuous hN rho₁ rho₂ rho₃).continuousAt
  rw [Real.fourierInv_eq] at hi
  simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def,
    smul_eq_mul, ← charReal_eq_fourierChar, fourier_tripleConvolution hN] at hi
  rw [← hi]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with eta
  simp only [neg_mul, mul_neg, neg_neg, mul_assoc]

end LiuWang.Proof.SingularIntegral
