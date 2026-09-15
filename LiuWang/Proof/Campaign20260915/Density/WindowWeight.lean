import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Kernel

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

namespace LiuWang.Proof.Campaign20260915.Density

theorem weighted_window_integral {v w B : ℝ → ℝ} {y C : ℝ}
    (hy : 0 < y) (hC : 0 ≤ C) (hv : Continuous v) (hw : Continuous w)
    (hv0 : ∀ t, 0 ≤ v t) (hw0 : ∀ t, 0 ≤ w t)
    (hB0 : ∀ u, 0 ≤ u → 0 ≤ B u)
    (hB : IntegrableOn (fun u => sourceKernel u * B u) (Ioi 0))
    (hwindow : ∀ u, 0 ≤ u → (∫ t in -(y * u)..y * u, v t) ≤ B u)
    (henv : ∀ t, w t ≤ C * (v t / (2 + Real.exp (|t| / y)))) :
    Integrable w ∧ (∫ t : ℝ, w t) ≤ C * ∫ u in Ioi (0 : ℝ), sourceKernel u * B u := by
  have htail := sourceKernel_window_identity hv.measurable y hy
  have hwin (u : ℝ) (hu : 0 ≤ u) :
      (∫⁻ t in Icc (-(y * u)) (y * u), ENNReal.ofReal (v t)) ≤ ENNReal.ofReal (B u) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hv.integrableOn_Icc
      (Eventually.of_forall hv0)]
    have h := hwindow u hu
    rw [intervalIntegral.integral_of_le (by nlinarith : -(y * u) ≤ y * u),
      ← integral_Icc_eq_integral_Ioc] at h
    exact ENNReal.ofReal_le_ofReal h
  have hBn : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ sourceKernel u * B u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (sourceKernel_pos u).le (hB0 u hu.le)
  have hR0 : 0 ≤ C * ∫ u in Ioi (0 : ℝ), sourceKernel u * B u :=
    mul_nonneg hC (integral_nonneg_of_ae hBn)
  have hlim : (∫⁻ t : ℝ, ENNReal.ofReal (w t)) ≤
      ENNReal.ofReal (C * ∫ u in Ioi (0 : ℝ), sourceKernel u * B u) := by
    calc
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal
          (C * (v t / (2 + Real.exp (|t| / y)))) :=
        lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (henv t))
      _ = ENNReal.ofReal C *
          ∫⁻ t : ℝ, ENNReal.ofReal (v t) *
            ENNReal.ofReal (1 / (2 + Real.exp (|t| / y))) := by
        have he (t : ℝ) :
            ENNReal.ofReal (C * (v t / (2 + Real.exp (|t| / y)))) =
              ENNReal.ofReal C * (ENNReal.ofReal (v t) *
                ENNReal.ofReal (1 / (2 + Real.exp (|t| / y)))) := by
          rw [ENNReal.ofReal_mul hC,
            show v t / (2 + Real.exp (|t| / y)) =
              v t * (1 / (2 + Real.exp (|t| / y))) by ring,
            ENNReal.ofReal_mul (hv0 t)]
        simp_rw [he]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal C *
          ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (sourceKernel u) *
            ∫⁻ t in Icc (-(y * u)) (y * u), ENNReal.ofReal (v t) := by rw [htail]
      _ ≤ ENNReal.ofReal C *
          ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (sourceKernel u) * ENNReal.ofReal (B u) := by
        apply mul_le_mul le_rfl _ zero_le zero_le
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact mul_le_mul le_rfl (hwin u hu.le) zero_le zero_le
      _ = _ := by
        simp_rw [← ENNReal.ofReal_mul (sourceKernel_pos _).le]
        rw [← ofReal_integral_eq_lintegral_ofReal hB hBn, ENNReal.ofReal_mul hC]
  have hi : Integrable w := by
    apply (lintegral_ofReal_ne_top_iff_integrable hw.aestronglyMeasurable
      (Eventually.of_forall hw0)).mp
    exact ne_of_lt (hlim.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hw0)] at hlim
  exact (ENNReal.ofReal_le_ofReal_iff hR0).mp hlim

#print axioms weighted_window_integral

end LiuWang.Proof.Campaign20260915.Density
