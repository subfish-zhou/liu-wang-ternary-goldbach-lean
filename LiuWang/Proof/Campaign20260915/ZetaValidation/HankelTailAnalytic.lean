import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelFixedContour
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Asymptotics
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsTruncatedMellinKernel (m : ℕ) (r : ℝ) : ℝ → ℂ :=
  (Ioi r).indicator (fun y => rsMellinTailKernel m (2 * Real.pi * y))

theorem rsScaledMellin_continuous (m : ℕ) :
    ContinuousOn (fun y : ℝ => rsMellinTailKernel m (2 * Real.pi * y)) (Ioi 0) := by
  intro y hy
  have hy0 : 0 < y := hy
  apply ContinuousAt.continuousWithinAt
  unfold rsMellinTailKernel
  apply continuous_ofReal.continuousAt.comp
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr (by positivity)))

theorem rsScaledMellin_tail_bound (m : ℕ) {r y : ℝ} (hr : 0 < r) (hy : r ≤ y) :
    ‖rsMellinTailKernel m (2 * Real.pi * y)‖ ≤
      (Real.exp (2 * Real.pi * r) - 1)⁻¹ * Real.exp (-(2 * Real.pi * m) * y) := by
  have hd : 0 < Real.exp (2 * Real.pi * r) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hdy : Real.exp (2 * Real.pi * r) - 1 ≤ Real.exp (2 * Real.pi * y) - 1 :=
    sub_le_sub_right (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) _
  rw [rsMellinTailKernel, norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (Real.exp_pos _) (lt_of_lt_of_le hd hdy))]
  have he : -(m : ℝ) * (2 * Real.pi * y) = -(2 * Real.pi * m) * y := by ring
  rw [he, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hd hdy

theorem rsTruncatedMellin_integrable {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    Integrable (rsTruncatedMellinKernel m r) := by
  rw [rsTruncatedMellinKernel, integrable_indicator_iff measurableSet_Ioi]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity : 0 < 2 * Real.pi * (m : ℝ))) r).const_mul
    (Real.exp (2 * Real.pi * r) - 1)⁻¹).mono'
  · exact ((rsScaledMellin_continuous m).mono (Ioi_subset_Ioi hr.le)).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact rsScaledMellin_tail_bound m hr hy.le

theorem rsTruncatedMellin_exp_decay (m : ℕ) {r : ℝ} (hr : 0 < r) :
    rsTruncatedMellinKernel m r =O[atTop] (fun y : ℝ => Real.exp (-(2 * Real.pi * m) * y)) := by
  apply isBigO_iff.mpr
  refine ⟨(Real.exp (2 * Real.pi * r) - 1)⁻¹, ?_⟩
  filter_upwards [eventually_gt_atTop r] with y hy
  rw [rsTruncatedMellinKernel, indicator_of_mem (show y ∈ Ioi r from hy),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact rsScaledMellin_tail_bound m hr hy.le

theorem rsTruncatedMellin_zero_near_origin (m : ℕ) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    rsTruncatedMellinKernel m r =O[𝓝[>] 0] (fun y : ℝ => y ^ (-b)) := by
  apply isBigO_iff.mpr
  refine ⟨0, ?_⟩
  filter_upwards [(eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with y hy
  rw [rsTruncatedMellinKernel, indicator_of_notMem (show y ∉ Ioi r from not_lt.mpr hy.le),
    norm_zero, zero_mul]

theorem rsTruncatedMellin_convergent {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) (s : ℂ) :
    MellinConvergent (rsTruncatedMellinKernel m r) s := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  exact mellinConvergent_of_isBigO_rpow_exp (by positivity : 0 < 2 * Real.pi * (m : ℝ))
    ((rsTruncatedMellin_integrable hm hr).locallyIntegrable.locallyIntegrableOn _)
    (rsTruncatedMellin_exp_decay m hr) (rsTruncatedMellin_zero_near_origin m hr (s.re - 1))
    (by linarith)

theorem rsTruncatedMellin_differentiable {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (mellin (rsTruncatedMellinKernel m r)) := by
  intro s
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by positivity : 0 < 2 * Real.pi * (m : ℝ))
    ((rsTruncatedMellin_integrable hm hr).locallyIntegrable.locallyIntegrableOn _)
    (rsTruncatedMellin_exp_decay m hr) (rsTruncatedMellin_zero_near_origin m hr (s.re - 1))
    (by linarith)

theorem rsTruncatedMellin_eq_integral (m : ℕ) {r : ℝ} (hr : 0 < r) (s : ℂ) :
    mellin (rsTruncatedMellinKernel m r) s =
      ∫ y : ℝ in Ioi r, (y : ℂ) ^ (s - 1) * rsMellinTailKernel m (2 * Real.pi * y) := by
  simp_rw [mellin, rsTruncatedMellinKernel, ← indicator_smul]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hr.le)]
  rfl

theorem rsHankelBanks_tail_integrable {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) (s : ℂ) :
    IntegrableOn (rsHankelRightBank s m) (Ioi r) ∧
      IntegrableOn (rsHankelLeftBank s m) (Ioi r) := by
  have h := rsTruncatedMellin_convergent hm hr s
  simp_rw [MellinConvergent, rsTruncatedMellinKernel, ← indicator_smul] at h
  rw [integrableOn_indicator_iff measurableSet_Ioi] at h
  rw [inter_eq_left.mpr (Ioi_subset_Ioi hr.le)] at h
  have hh := h.const_mul (exp (-(Real.pi / 2 : ℂ) * I * s))
  have hright : IntegrableOn (rsHankelRightBank s m) (Ioi r) := by
    apply IntegrableOn.congr_fun hh _ measurableSet_Ioi
    intro y _
    simp only [rsHankelRightBank, smul_eq_mul]
    ring
  exact ⟨hright, hright.const_mul _⟩

theorem rsHankelBank_tail_differentiable {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (fun s : ℂ => ∫ y : ℝ in Ioi r, rsHankelRightBank s m y) ∧
      Differentiable ℂ (fun s : ℂ => ∫ y : ℝ in Ioi r, rsHankelLeftBank s m y) := by
  have he (s : ℂ) : (∫ y : ℝ in Ioi r, rsHankelRightBank s m y) =
      exp (-(Real.pi / 2 : ℂ) * I * s) * mellin (rsTruncatedMellinKernel m r) s := by
    rw [rsTruncatedMellin_eq_integral m hr]
    simp_rw [rsHankelRightBank, mul_assoc]
    rw [integral_const_mul]
  have hd : Differentiable ℂ (fun s : ℂ => ∫ y : ℝ in Ioi r, rsHankelRightBank s m y) := by
    simp_rw [he]
    exact (show Differentiable ℂ (fun s : ℂ => exp (-(Real.pi / 2 : ℂ) * I * s)) by
      fun_prop).mul (rsTruncatedMellin_differentiable hm hr)
  refine ⟨hd, ?_⟩
  simp_rw [rsHankelLeftBank, integral_const_mul]
  exact (show Differentiable ℂ (fun s : ℂ => exp (2 * Real.pi * I * s)) by fun_prop).mul hd

end LiuWang.Proof.Campaign20260915.ZetaValidation
