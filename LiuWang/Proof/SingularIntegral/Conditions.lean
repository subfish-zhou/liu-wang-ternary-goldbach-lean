import LiuWang.Proof.SingularIntegral.Convolution

/-! # 显式导出每一个点的卷积可积性条件 -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Convolution

namespace LiuWang.Proof.SingularIntegral

theorem convolution_integrand_integrable_of_bounded_right
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : StronglyMeasurable g)
    {C : ℝ} (hC : ∀ t : ℝ, ‖g t‖ ≤ C) (x : ℝ) :
    Integrable (fun t : ℝ => f t * g (x - t)) := by
  refine (hf.norm.mul_const C).mono'
    (hf.aestronglyMeasurable.mul
      (hg.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

theorem window_pair_convolutionExists {N : ℕ} (hN : 0 < N) (rho₁ rho₂ : ℂ) :
    ConvolutionExists (windowWeight N rho₁) (windowWeight N rho₂)
      (ContinuousLinearMap.mul ℂ ℂ) := by
  obtain ⟨C, _, hC⟩ := windowWeight_bounded hN rho₂
  exact fun x => convolution_integrand_integrable_of_bounded_right
    (windowWeight_integrable hN rho₁) (windowWeight_stronglyMeasurable N rho₂) hC x

theorem window_triple_convolutionExists {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    ConvolutionExists (windowWeight N rho₁)
      (windowWeight N rho₂ ⋆[ContinuousLinearMap.mul ℂ ℂ] windowWeight N rho₃)
      (ContinuousLinearMap.mul ℂ ℂ) := by
  obtain ⟨C, hC⟩ := convolution_window_bounded hN rho₃ (windowWeight_integrable hN rho₂)
  exact fun x => convolution_integrand_integrable_of_bounded_right
    (windowWeight_integrable hN rho₁)
    (convolution_window_continuous hN rho₃ (windowWeight_integrable hN rho₂)).stronglyMeasurable
    (fun t => hC (mem_range_self t)) x

end LiuWang.Proof.SingularIntegral
