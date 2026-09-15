import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RSSection8Scalar

def logTailKernel (a n y : ℝ) : ℝ :=
  y ^ (a - n - 1) * (1 + n * Real.log y) / Real.log y ^ 2

private def majorant (a n y : ℝ) : ℝ :=
  n / (n - a) * y ^ (a - n - 1) *
    (1 + (n - a) * Real.log y) / Real.log y ^ 2

private theorem majorant_deriv {a n y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun t : ℝ => -(n / (n - a) * t ^ (a - n) / Real.log t))
      (majorant a n y) y := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hl := Real.log_pos hy
  have hd := (((Real.hasDerivAt_rpow_const (p := a - n) (Or.inl hy0.ne')).const_mul
    (n / (n - a))).div (Real.hasDerivAt_log hy0.ne') hl.ne').neg
  convert! hd using 1
  rw [show a - n = (a - n - 1) + 1 by ring,
    Real.rpow_add hy0, Real.rpow_one]
  unfold majorant
  field_simp
  ring

private theorem majorant_nonneg {a n y : ℝ} (ha : 0 ≤ a) (han : a < n)
    (hy : 1 < y) : 0 ≤ majorant a n y := by
  have hn : 0 < n := lt_of_le_of_lt ha han
  have hl := (Real.log_pos hy).le
  unfold majorant
  positivity

private theorem kernel_le_majorant {a n y : ℝ} (ha : 0 ≤ a) (han : a < n)
    (hy : 1 < y) : logTailKernel a n y ≤ majorant a n y := by
  have hd : 0 < n - a := sub_pos.mpr han
  have hp : 0 ≤ y ^ (a - n - 1) := Real.rpow_nonneg (by linarith) _
  unfold logTailKernel majorant
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h : 1 + n * Real.log y ≤ n / (n - a) * (1 + (n - a) * Real.log y) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h hp]

private theorem majorant_tendsto {a n : ℝ} (han : a < n) :
    Tendsto (fun t : ℝ => -(n / (n - a) * t ^ (a - n) / Real.log t))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t ^ (a - n)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr han)
  simpa [div_eq_mul_inv] using
    ((hp.const_mul (n / (n - a))).mul Real.tendsto_log_atTop.inv_tendsto_atTop).neg

theorem logTailKernel_nonneg {a n y : ℝ} (ha : 0 ≤ a) (han : a < n)
    (hy : 1 < y) : 0 ≤ logTailKernel a n y := by
  have hn : 0 < n := lt_of_le_of_lt ha han
  have hl := (Real.log_pos hy).le
  unfold logTailKernel
  positivity

theorem logTailKernel_integrable {a n x : ℝ} (ha : 0 ≤ a) (han : a < n)
    (hx : 1 < x) : IntegrableOn (logTailKernel a n) (Ioi x) := by
  have hi := integrableOn_Ioi_deriv_of_nonneg'
    (fun y (hy : y ∈ Ici x) => majorant_deriv (hx.trans_le hy))
    (fun y (hy : y ∈ Ioi x) => majorant_nonneg ha han (hx.trans hy))
    (majorant_tendsto han)
  apply hi.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro y hy
    have hy1 := hx.trans hy
    have hy0 : 0 < y := lt_trans zero_lt_one hy1
    exact (((Real.continuousAt_rpow_const _ _ (Or.inl hy0.ne')).mul
      (continuousAt_const.add ((Real.continuousAt_log hy0.ne').const_mul n))).div
      ((Real.continuousAt_log hy0.ne').pow 2) (pow_ne_zero 2 (Real.log_pos hy1).ne')
      ).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (logTailKernel_nonneg ha han (hx.trans hy))]
    exact kernel_le_majorant ha han (hx.trans hy)

/-- RS1962, p.85, Lemma 9, with its implicit `x > 1` made explicit. -/
theorem lemma9 {a n x : ℝ} (ha : 0 ≤ a) (han : a < n) (hx : 1 < x) :
    (∫ y in Ioi x, logTailKernel a n y) ≤
      n / (n - a) * (x ^ (a - n) / Real.log x) := by
  have hd := fun y (hy : y ∈ Ici x) => majorant_deriv (a := a) (n := n) (hx.trans_le hy)
  have hn := fun y (hy : y ∈ Ioi x) => majorant_nonneg ha han (hx.trans hy)
  have ht := majorant_tendsto han
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hn ht
  calc
    _ ≤ ∫ y in Ioi x, majorant a n y :=
      setIntegral_mono_on (logTailKernel_integrable ha han hx) hi measurableSet_Ioi
        (fun y hy => kernel_le_majorant ha han (hx.trans hy))
    _ = _ := by rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht]; ring

#print axioms logTailKernel_integrable
#print axioms lemma9

end LiuWang.Proof.Campaign20260915.RSSection8Scalar
