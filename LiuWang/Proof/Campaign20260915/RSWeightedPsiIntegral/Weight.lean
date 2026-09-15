import LiuWang.Proof.Campaign20260915.Totient.RSZeroIntegration
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def weight (x : ℝ) : ℝ := (1 + Real.log x) / (x ^ 2 * Real.log x ^ 2)

def scaledWeight (x : ℝ) : ℝ := (1 + Real.log x) / Real.log x ^ 2

def weightSlope (x : ℝ) : ℝ :=
  -(2 * Real.log x ^ 2 + 3 * Real.log x + 2) / (x ^ 3 * Real.log x ^ 3)

theorem weight_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ weight x := by
  have hl := Real.log_pos hx
  unfold weight
  positivity

theorem scaledWeight_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ scaledWeight x := by
  have hl := Real.log_pos hx
  unfold scaledWeight
  positivity

theorem weight_eq_scaled (x : ℝ) : weight x = scaledWeight x / x ^ 2 := by
  unfold weight scaledWeight
  ring

theorem scaledWeight_eq {x : ℝ} (hx : 1 < x) :
    scaledWeight x = (Real.log x)⁻¹ ^ 2 + (Real.log x)⁻¹ := by
  have hl := (Real.log_pos hx).ne'
  unfold scaledWeight
  field_simp

theorem scaledWeight_tendsto_zero :
    Tendsto scaledWeight atTop (𝓝 0) := by
  have h := Real.tendsto_log_atTop.inv_tendsto_atTop
  have hh := (h.pow 2).add h
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (scaledWeight_eq hx).symm

theorem weight_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt weight (weightSlope x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  convert! ((Real.hasDerivAt_log hx0).const_add 1).div
    (((hasDerivAt_id x).pow 2).mul ((Real.hasDerivAt_log hx0).pow 2))
    (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hl)) using 1
  simp only [weightSlope, Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one]
  field_simp
  ring

theorem weight_continuousOn : ContinuousOn weight (Ioi 1) :=
  fun _ hx => (weight_hasDerivAt hx).continuousAt.continuousWithinAt

theorem weightSlope_continuousOn : ContinuousOn weightSlope (Ioi 1) := by
  apply ContinuousOn.div
  · exact ((Real.continuousOn_log.mono (fun x hx => by
      have : 1 < x := hx
      simp only [mem_compl_iff, mem_singleton_iff]
      linarith)).pow 2 |>.const_mul 2 |>.add
        ((Real.continuousOn_log.mono (fun x hx => by
          have : 1 < x := hx
          simp only [mem_compl_iff, mem_singleton_iff]
          linarith)).const_mul 3) |>.add continuousOn_const).neg
  · exact (continuousOn_id.pow 3).mul
      ((Real.continuousOn_log.mono (fun x hx => by
        have : 1 < x := hx
        simp only [mem_compl_iff, mem_singleton_iff]
        linarith)).pow 3)
  · intro x hx
    exact mul_ne_zero (pow_ne_zero _ (by have : 1 < x := hx; linarith))
      (pow_ne_zero _ (Real.log_pos hx).ne')

theorem inv_mul_log_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y => (y * Real.log y)⁻¹) (-weight x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  convert! (((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv
    (mul_ne_zero hx0 hl)) using 1
  · simp only [weight, Pi.mul_apply, id_eq, one_mul]
    field_simp
    ring

theorem inv_mul_log_tendsto_zero :
    Tendsto (fun x : ℝ => (x * Real.log x)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.mul Real.tendsto_log_atTop.inv_tendsto_atTop
  simpa only [mul_inv, mul_zero, Pi.inv_apply] using h

theorem weight_integrableOn {x : ℝ} (hx : 1 < x) :
    IntegrableOn weight (Ioi x) := by
  have h := integrableOn_Ioi_deriv_of_nonpos'
    (fun y (hy : y ∈ Ici x) => inv_mul_log_hasDerivAt (hx.trans_le hy))
    (fun y (hy : y ∈ Ioi x) => neg_nonpos.mpr (weight_nonneg (hx.trans hy)))
    inv_mul_log_tendsto_zero
  exact h.neg.congr (Filter.Eventually.of_forall (fun y => neg_neg (weight y)))

theorem weight_integral_Ioi {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, weight y) = 1 / (x * Real.log x) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y (hy : y ∈ Ici x) => inv_mul_log_hasDerivAt (hx.trans_le hy))
    (weight_integrableOn hx).neg inv_mul_log_tendsto_zero
  rw [integral_neg, zero_sub] at h
  simpa only [one_div] using neg_injective h

theorem zeroPrimitive_weight_norm_bound (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 1 < x) :
    ‖rsZeroPrimitive 1 x p * (weight x : ℂ)‖ ≤
      rsZeroMoment 1 0 p * scaledWeight x := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hx)]
  apply (mul_le_mul_of_nonneg_right
    (rsZeroPrimitive_compact_bound 1 p hx.le le_rfl) (weight_nonneg hx)).trans_eq
  rw [weight_eq_scaled]
  have hx0 : x ≠ 0 := by linarith
  norm_num only [Nat.reduceAdd]
  field_simp

theorem zeroSum_weight_norm_bound {x : ℝ} (hx : 1 < x) :
    ‖(∑' p, rsZeroPrimitive 1 x p) * (weight x : ℂ)‖ ≤
      (∑' p, rsZeroMoment 1 0 p) * scaledWeight x := by
  rw [← tsum_mul_right]
  have hs := (rsZeroPrimitive_summable (by omega : 1 ≤ 1) hx.le).mul_right (weight x : ℂ)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum (fun p => zeroPrimitive_weight_norm_bound p hx)
      ((rsZeroMoment_summable (by omega : 1 ≤ 1) (le_refl (0 : ℝ))).mul_right
        (scaledWeight x))).trans_eq tsum_mul_right)

theorem zeroSum_weight_tendsto_zero :
    Tendsto (fun x => (∑' p, rsZeroPrimitive 1 x p) * (weight x : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun x =>
    (∑' p, rsZeroMoment 1 0 p) * scaledWeight x)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact zeroSum_weight_norm_bound hx
  · simpa only [mul_zero] using
      scaledWeight_tendsto_zero.const_mul (∑' p, rsZeroMoment 1 0 p)

#print axioms weight_integral_Ioi
#print axioms zeroSum_weight_tendsto_zero

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
