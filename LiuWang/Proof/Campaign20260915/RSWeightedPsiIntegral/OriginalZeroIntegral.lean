import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.Lemma8

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def zeroIntegrand (p : RiemannXiDivisorZeroIndex) (y : ℝ) : ℂ :=
  rsZeroPrimitive 0 y p * (weight y : ℂ)

theorem zeroIntegrand_norm (p : RiemannXiDivisorZeroIndex) {y : ℝ} (hy : 1 < y) :
    ‖zeroIntegrand p y‖ =
      y ^ ((riemannXiDivisorZeroValue p).re - 2) *
        (scaledWeight y / ‖riemannXiDivisorZeroValue p‖) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  simp only [zeroIntegrand, rsZeroPrimitive, Nat.cast_zero, add_zero,
    Finset.prod_range_succ, Finset.prod_range_zero, one_mul, norm_mul, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg hy)]
  rw [weight_eq_scaled, Real.rpow_sub hy0, Real.rpow_two]
  ring

theorem zeroIntegrand_integrable (p : RiemannXiDivisorZeroIndex) {x : ℝ} (hx : 1 < x) :
    IntegrableOn (zeroIntegrand p) (Ioi x) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have he : (riemannXiDivisorZeroValue p).re - 2 < -1 := by
    linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]
  refine ((integrableOn_Ioi_rpow_of_lt he hx0).mul_const
    (scaledWeight x / ‖riemannXiDivisorZeroValue p‖)).mono'
    (by
      apply Measurable.aestronglyMeasurable
      unfold zeroIntegrand rsZeroPrimitive weight
      fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [zeroIntegrand_norm p (hx.trans hy)]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (scaledWeight_antitone hx (hx.trans hy) hy.le)
      (norm_nonneg _)) (Real.rpow_nonneg (hx0.trans hy).le _)

theorem original_zero_integral_eq (p : RiemannXiDivisorZeroIndex) {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, zeroIntegrand p y) = integratedZeroTail p x := by
  have hd (y : ℝ) (hy : y ∈ Ici x) :
      HasDerivAt (fun t => rsZeroPrimitive 1 t p * (weight t : ℂ))
        (zeroIntegrand p y + rsZeroPrimitive 1 y p * (weightSlope y : ℂ)) y := by
    exact (rsZeroPrimitive_deriv 0 p (lt_trans zero_lt_one (hx.trans_le hy))).mul
      (weight_hasDerivAt (hx.trans_le hy)).ofReal_comp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((zeroIntegrand_integrable p hx).add (zeroPrimitive_slope_integrable p hx))
    (zeroPrimitive_weight_tendsto_zero p)
  rw [integral_add (zeroIntegrand_integrable p hx) (zeroPrimitive_slope_integrable p hx),
    zero_sub] at h
  unfold integratedZeroTail
  linear_combination h

theorem original_zero_integrals_summable {x : ℝ} (hx : 1 < x) :
    Summable (fun p => ∫ y in Ioi x, zeroIntegrand p y) := by
  exact (integratedZeroTail_summable hx).congr
    (fun p => (original_zero_integral_eq p hx).symm)

theorem actual_original_zero_integral_identity {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, signedPsiError y) =
      (∑' p, ∫ y in Ioi x, zeroIntegrand p y).re +
        ∫ y in Ioi x, signedCorrection y := by
  simp_rw [original_zero_integral_eq _ hx]
  exact actual_infinite_zero_tail_identity hx

theorem original_zero_integral_norm_bound (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 1 < x) :
    ‖∫ y in Ioi x, zeroIntegrand p y‖ ≤
      rsZeroMoment 1 (Real.log x) p * lemma8Factor x := by
  rw [original_zero_integral_eq p hx]
  exact integratedZeroTail_norm_bound p hx

#print axioms zeroIntegrand_integrable
#print axioms original_zero_integrals_summable
#print axioms actual_original_zero_integral_identity
#print axioms original_zero_integral_norm_bound

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
