import LiuWang.Proof.GlobalZeroDensity.Strip.Window
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Fubini for exponentially weighted actual symmetric-window integrals. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace LiuWang.Proof.GlobalZeroDensity.Strip

theorem exponential_tail_integral {r : ℝ} (hr : 0 < r) (a : ℝ) :
    (∫ u in Ici a, Real.exp (-u / r) / r) = Real.exp (-a / r) := by
  rw [integral_div, integral_Ici_eq_integral_Ioi]
  have h := integral_exp_mul_Ioi (a := -(r⁻¹)) (neg_neg_of_pos (inv_pos.mpr hr)) a
  have he (u : ℝ) : -u / r = -(r⁻¹) * u := by ring
  simp_rw [he]
  rw [h]
  field_simp

theorem exponential_window_identity {v : ℝ → ℝ} (hv : Continuous v)
    (hv0 : ∀ t, 0 ≤ v t) {r : ℝ} (hr : 0 < r)
    (hmean : IntegrableOn (fun u : ℝ => Real.exp (-u / r) / r * (∫ t in -u..u, v t))
      (Ici 0)) :
    Integrable (fun t : ℝ => v t * Real.exp (-|t| / r)) ∧
      (∫ t : ℝ, v t * Real.exp (-|t| / r)) =
        ∫ u in Ici (0 : ℝ), Real.exp (-u / r) / r * (∫ t in -u..u, v t) := by
  let kernel (p : ℝ × ℝ) : ℝ :=
    {p : ℝ × ℝ | |p.2| ≤ p.1}.indicator
      (fun p => Real.exp (-p.1 / r) / r * v p.2) p
  have hk0 (u t : ℝ) : 0 ≤ kernel (u, t) := by
    apply indicator_nonneg
    intro p _
    exact mul_nonneg (by positivity) (hv0 p.2)
  have hkm : AEStronglyMeasurable kernel ((volume.restrict (Ici 0)).prod volume) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator
    · exact ((Real.measurable_exp.comp (measurable_fst.neg.div_const r)).div_const r).mul
        (hv.measurable.comp measurable_snd)
    · exact measurableSet_le measurable_snd.abs measurable_fst
  have hslice (u : ℝ) : (fun t => kernel (u, t)) =
      (Icc (-u) u).indicator (fun t => Real.exp (-u / r) / r * v t) := by
    funext t
    simp only [kernel, indicator_apply, mem_ofPred_eq, mem_Icc, abs_le]
  have hinner (u : ℝ) (hu : 0 ≤ u) :
      (∫ t, kernel (u, t)) = Real.exp (-u / r) / r * (∫ t in -u..u, v t) := by
    rw [hslice, integral_indicator measurableSet_Icc, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
  have hk : Integrable kernel ((volume.restrict (Ici 0)).prod volume) := by
    apply (integrable_prod_iff hkm).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u _hu
      rw [hslice]
      exact ((hv.const_mul _).continuousOn.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · have he : (fun u : ℝ => ∫ t, ‖kernel (u, t)‖) =ᵐ[volume.restrict (Ici 0)]
          (fun u : ℝ => Real.exp (-u / r) / r * (∫ t in -u..u, v t)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
        simp only [Real.norm_of_nonneg (hk0 u _)]
        exact hinner u hu
      exact hmean.congr he.symm
  have hswap (t : ℝ) : (∫ u in Ici (0 : ℝ), kernel (u, t)) =
      v t * Real.exp (-|t| / r) := by
    have he : (fun u => kernel (u, t)) =
        (Ici |t|).indicator (fun u => Real.exp (-u / r) / r * v t) := by
      funext u
      simp only [kernel, indicator_apply, mem_ofPred_eq, mem_Ici]
    rw [he, setIntegral_indicator measurableSet_Ici, Ici_inter_Ici,
      max_eq_right (abs_nonneg t), integral_mul_const, exponential_tail_integral hr]
    ring
  have hint := hk.integral_prod_right
  simp_rw [hswap] at hint
  refine ⟨hint, ?_⟩
  have h := integral_integral_swap (f := fun u t => kernel (u, t)) hk
  simp_rw [hswap] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact hinner u hu

end LiuWang.Proof.GlobalZeroDensity.Strip
