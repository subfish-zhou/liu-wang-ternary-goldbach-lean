import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.ZeroTailKernel

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

theorem zeroPrimitive_weight_tendsto_zero (p : RiemannXiDivisorZeroIndex) :
    Tendsto (fun x => rsZeroPrimitive 1 x p * (weight x : ℂ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun y => rsZeroMoment 1 0 p * scaledWeight y)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    exact zeroPrimitive_weight_norm_bound p hy
  · simpa only [mul_zero] using scaledWeight_tendsto_zero.const_mul (rsZeroMoment 1 0 p)

theorem integratedZeroTail_eq (p : RiemannXiDivisorZeroIndex) {x : ℝ} (hx : 1 < x) :
    integratedZeroTail p x = -zeroBoundary p x + ∫ y in Ioi x, zeroRemainder p y := by
  have hd (y : ℝ) (hy : y ∈ Ici x) :
      HasDerivAt (fun t => rsZeroPrimitive 1 t p * (weight t : ℂ) - zeroBoundary p t)
        (rsZeroPrimitive 1 y p * (weightSlope y : ℂ) + zeroRemainder p y) y := by
    have hy1 : 1 < y := hx.trans_le hy
    have h := ((rsZeroPrimitive_deriv 0 p (lt_trans zero_lt_one hy1)).mul
      (weight_hasDerivAt hy1).ofReal_comp).sub (zeroBoundary_hasDerivAt p hy1)
    convert! h using 1
    ring
  have hl := (zeroPrimitive_weight_tendsto_zero p).sub (zeroBoundary_tendsto_zero p)
  simp only [sub_zero] at hl
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((zeroPrimitive_slope_integrable p hx).add (zeroRemainder_integrable p hx)) hl
  rw [integral_add (zeroPrimitive_slope_integrable p hx) (zeroRemainder_integrable p hx),
    zero_sub] at h
  unfold integratedZeroTail
  linear_combination -h

theorem integratedZeroTail_norm_bound (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 1 < x) :
    ‖integratedZeroTail p x‖ ≤ rsZeroMoment 1 (Real.log x) p * lemma8Factor x := by
  rw [integratedZeroTail_eq p hx]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  apply (add_le_add (zeroBoundary_norm_bound p hx)
    (zeroRemainder_integral_norm_bound p hx)).trans_eq
  unfold scaledWeight lemma8Factor
  ring

theorem integratedZeroTail_summable {x : ℝ} (hx : 1 < x) :
    Summable (fun p => integratedZeroTail p x) :=
  ((rsZeroMoment_summable (by omega : 1 ≤ 1) (Real.log_nonneg hx.le)).mul_right
    (lemma8Factor x)).of_norm_bounded (fun p => integratedZeroTail_norm_bound p hx)

theorem zeroSlope_integrals_summable {x : ℝ} (hx : 1 < x) :
    Summable (fun p => ∫ y in Ioi x, rsZeroPrimitive 1 y p * (weightSlope y : ℂ)) := by
  have hz := (rsZeroPrimitive_summable (by omega : 1 ≤ 1) hx.le).mul_right (weight x : ℂ)
  exact (hz.neg.sub (integratedZeroTail_summable hx)).congr (fun p => by
    dsimp [integratedZeroTail]
    ring)

theorem actual_infinite_zero_tail_identity {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, signedPsiError y) =
      (∑' p, integratedZeroTail p x).re + ∫ y in Ioi x, signedCorrection y := by
  have hz := (rsZeroPrimitive_summable (by omega : 1 ≤ 1) hx.le).mul_right (weight x : ℂ)
  have he : (∑' p, integratedZeroTail p x) =
      -(∑' p, rsZeroPrimitive 1 x p) * (weight x : ℂ) -
        ∑' p, ∫ y in Ioi x, rsZeroPrimitive 1 y p * (weightSlope y : ℂ) := by
    simp_rw [integratedZeroTail, neg_mul]
    rw [hz.neg.tsum_sub (zeroSlope_integrals_summable hx), tsum_neg, tsum_mul_right]
  rw [he, actual_infinite_weighted_spectral_identity hx]
  simp [spectralPrimitive, Complex.sub_re, Complex.mul_re]

theorem zero_tail_sum_norm_bound {x : ℝ} (hx : 1 < x) :
    ‖∑' p, integratedZeroTail p x‖ ≤ momentSum x * lemma8Factor x := by
  have hs := integratedZeroTail_summable hx
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  have h := hs.norm.tsum_le_tsum (fun p => integratedZeroTail_norm_bound p hx)
    ((rsZeroMoment_summable (by omega : 1 ≤ 1) (Real.log_nonneg hx.le)).mul_right
      (lemma8Factor x))
  simpa only [tsum_mul_right, momentSum] using h

theorem lemma8_moment {x : ℝ} (hx : 1 < x) :
    |∫ y in Ioi x, signedPsiError y| <
      lemma8Factor x * (momentSum x + (184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3) := by
  rw [actual_infinite_zero_tail_identity hx]
  have hz := (Complex.abs_re_le_norm (∑' p, integratedZeroTail p x)).trans
    (zero_tail_sum_norm_bound hx)
  apply (abs_add_le _ _).trans_lt
  apply (add_lt_add_of_le_of_lt hz (signedCorrection_integral_abs_lt hx)).trans_eq
  ring

theorem momentSum_eq_original_K {x : ℝ} (hx : 0 < x) :
    momentSum x =
      ∑' p : RiemannXiDivisorZeroIndex,
        x ^ ((riemannXiDivisorZeroValue p).re - 1) /
          |(riemannXiDivisorZeroValue p).im ^ (1 + 1)| := by
  unfold momentSum
  apply tsum_congr
  intro p
  rw [Real.rpow_def_of_pos hx, abs_pow]
  unfold rsZeroMoment
  rw [mul_comm (Real.log x)]

theorem lemma8 {x : ℝ} (hx : 1 < x) :
    |∫ y in Ioi x,
      (y - Chebyshev.psi y) * (1 + Real.log y) / (y ^ 2 * Real.log y ^ 2)| <
      (2 + Real.log x) / Real.log x ^ 2 *
        ((∑' p : RiemannXiDivisorZeroIndex,
          x ^ ((riemannXiDivisorZeroValue p).re - 1) /
            |(riemannXiDivisorZeroValue p).im ^ (1 + 1)|) +
          (184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3) := by
  have h := lemma8_moment hx
  rw [momentSum_eq_original_K (lt_trans zero_lt_one hx)] at h
  simpa only [signedPsiError, weight, lemma8Factor, mul_div_assoc] using h

theorem lemma13_psi_tail_lower {x : ℝ} (hx : 1 < x) :
    -(lemma8Factor x * (momentSum x + (184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3)) <
      ∫ y in Ioi x, signedPsiError y :=
  (abs_lt.mp (lemma8_moment hx)).1

theorem lemma13_psi_tail_upper {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, signedPsiError y) <
      lemma8Factor x * (momentSum x + (184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3) :=
  (abs_lt.mp (lemma8_moment hx)).2

#print axioms actual_infinite_zero_tail_identity
#print axioms lemma8
#print axioms lemma13_psi_tail_lower
#print axioms lemma13_psi_tail_upper

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
