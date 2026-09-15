import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.InfinitePsi

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def momentSum (y : ℝ) : ℝ := ∑' p, rsZeroMoment 1 (Real.log y) p

def zeroSlopeEnvelope (y : ℝ) : ℝ := y ^ 2 * momentSum y * |weightSlope y|

theorem momentTerm_nonneg (y : ℝ) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ rsZeroMoment 1 (Real.log y) p := by unfold rsZeroMoment; positivity

theorem momentTerm_le_zero {y : ℝ} (hy : 1 ≤ y) (p : RiemannXiDivisorZeroIndex) :
    rsZeroMoment 1 (Real.log y) p ≤ rsZeroMoment 1 0 p := by
  unfold rsZeroMoment
  simp only [mul_zero, Real.exp_zero]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]) (Real.log_nonneg hy)

theorem momentSum_continuousOn : ContinuousOn momentSum (Ioi 1) := by
  apply continuousOn_tsum
    (fun p => ?_) (rsZeroMoment_summable (by omega : 1 ≤ 1) (le_refl (0 : ℝ)))
  · intro p y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (momentTerm_nonneg y p)]
    exact momentTerm_le_zero hy.le p
  · intro y hy
    unfold rsZeroMoment
    have hl := Real.continuousAt_log (ne_of_gt (lt_trans zero_lt_one hy))
    exact ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul hl)).div_const _).continuousWithinAt

theorem momentSum_nonneg (y : ℝ) : 0 ≤ momentSum y :=
  tsum_nonneg (momentTerm_nonneg y)

theorem momentSum_le_log_sixth {y : ℝ} (hy : Real.exp 100 ≤ Real.log y) :
    momentSum y ≤ 1 / Real.log y ^ 6 := by
  have h := xiZeroWeight_sum_le_log_sixth hy
  simpa only [momentSum, rsZeroMoment, xiZeroWeight, Nat.reduceAdd, sq_abs] using h

theorem zeroSlopeEnvelope_continuousOn : ContinuousOn zeroSlopeEnvelope (Ioi 1) :=
  ((continuousOn_id.pow 2).mul momentSum_continuousOn).mul weightSlope_continuousOn.abs

theorem zeroSlopeEnvelope_nonneg (y : ℝ) : 0 ≤ zeroSlopeEnvelope y :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (momentSum_nonneg _)) (abs_nonneg _)

theorem zeroSlopeEnvelope_tail_bound {y : ℝ} (hy : 0 < y)
    (hlog : 2 * Real.exp 100 ≤ Real.log y) :
    zeroSlopeEnvelope y ≤ 7 * (y⁻¹ / Real.log y ^ 2) := by
  have hl1 : 1 ≤ Real.log y := le_trans (by norm_num) (log_large_of_tail hlog)
  have hl : 0 < Real.log y := lt_of_lt_of_le zero_lt_one hl1
  have hM := momentSum_le_log_sixth
    (le_trans (by linarith [Real.exp_pos 100] : Real.exp 100 ≤ 2 * Real.exp 100) hlog)
  have hL : Real.log y ≤ Real.log y ^ 2 := by nlinarith
  have hnum : 2 * Real.log y ^ 2 + 3 * Real.log y + 2 ≤ 7 * Real.log y ^ 2 := by
    nlinarith
  have hs : |weightSlope y| ≤ 7 / (y ^ 3 * Real.log y) := by
    rw [weightSlope, abs_div, abs_neg, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    apply (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq
    field_simp
  unfold zeroSlopeEnvelope
  calc
    _ ≤ y ^ 2 * (1 / Real.log y ^ 6) * (7 / (y ^ 3 * Real.log y)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hM (sq_nonneg y)) hs
        (abs_nonneg _) (by positivity)
    _ = 7 * y⁻¹ / Real.log y ^ 7 := by field_simp
    _ ≤ 7 * (y⁻¹ / Real.log y ^ 2) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hl1 (by omega : 2 ≤ 7))

theorem zeroSlopeEnvelope_integrableOn {x : ℝ} (hx : 1 < x) :
    IntegrableOn zeroSlopeEnvelope (Ioi x) := by
  let b := max x (Real.exp (2 * Real.exp 100))
  have hxb : x ≤ b := le_max_left _ _
  have hb : 1 < b := hx.trans_le hxb
  have hc : IntervalIntegrable zeroSlopeEnvelope volume x b :=
    (zeroSlopeEnvelope_continuousOn.mono (by
      rw [uIcc_of_le hxb]
      exact fun _ hy => hx.trans_le hy.1)).intervalIntegrable
  have ht : IntegrableOn zeroSlopeEnvelope (Ioi b) := by
    refine ((integrableOn_inv_div_log_sq_Ioi hb).const_mul 7).mono'
      ((zeroSlopeEnvelope_continuousOn.mono
        (fun _ hy => hb.trans hy)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (zeroSlopeEnvelope_nonneg y)]
    have hy0 : 0 < y := lt_trans (lt_trans zero_lt_one hb) hy
    exact zeroSlopeEnvelope_tail_bound hy0
      ((Real.le_log_iff_exp_le hy0).mpr ((le_max_right _ _).trans hy.le))
  rw [← Ioc_union_Ioi_eq_Ioi hxb]
  exact hc.1.union ht

theorem zeroPrimitive_slope_norm_bound (p : RiemannXiDivisorZeroIndex)
    {y : ℝ} (hy : 1 < y) :
    ‖rsZeroPrimitive 1 y p * (weightSlope y : ℂ)‖ ≤
      y ^ 2 * rsZeroMoment 1 (Real.log y) p * |weightSlope y| := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  simpa using rsZeroPrimitive_shift_bound 1 0 p (lt_trans zero_lt_one hy)
    (le_refl (0 : ℝ))

theorem zeroPrimitive_slope_integrable (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun y => rsZeroPrimitive 1 y p * (weightSlope y : ℂ)) (Ioi x) := by
  refine (zeroSlopeEnvelope_integrableOn hx).mono'
    (((rsZeroPrimitive_continuousOn 1 p).mono
      (fun _ hy => lt_trans zero_lt_one (hx.trans hy))).mul
      (Complex.continuous_ofReal.comp_continuousOn
        (weightSlope_continuousOn.mono (fun _ hy => hx.trans hy)))
      |>.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  apply (zeroPrimitive_slope_norm_bound p (hx.trans hy)).trans
  have hp := (rsZeroMoment_summable (by omega : 1 ≤ 1) (Real.log_nonneg (hx.trans hy).le)
    ).le_tsum p (fun q _ => momentTerm_nonneg y q)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (sq_nonneg y))
    (abs_nonneg _)

theorem zeroSum_slope_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun y => (∑' p, rsZeroPrimitive 1 y p) * (weightSlope y : ℂ))
      (Ioi x) := by
  refine (zeroSlopeEnvelope_integrableOn hx).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.tsum
      intro p
      unfold rsZeroPrimitive
      fun_prop
    · unfold weightSlope
      fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [← tsum_mul_right]
    have hs := (rsZeroPrimitive_summable (by omega : 1 ≤ 1) (hx.trans hy).le).mul_right
      (weightSlope y : ℂ)
    apply (norm_tsum_le_tsum_norm hs.norm).trans
    have h := hs.norm.tsum_le_tsum (fun p => zeroPrimitive_slope_norm_bound p (hx.trans hy))
      (((rsZeroMoment_summable (by omega : 1 ≤ 1) (Real.log_nonneg (hx.trans hy).le)
        ).mul_left (y ^ 2)).mul_right |weightSlope y|)
    simpa only [tsum_mul_right, tsum_mul_left, zeroSlopeEnvelope, momentSum] using h

theorem zeroSum_slope_integral_exchange {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, (∑' p, rsZeroPrimitive 1 y p) * (weightSlope y : ℂ)) =
      ∑' p, ∫ y in Ioi x, rsZeroPrimitive 1 y p * (weightSlope y : ℂ) := by
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi x))
    (F := fun p y => rsZeroPrimitive 1 y p * (weightSlope y : ℂ))
    (f := fun y => (∑' p, rsZeroPrimitive 1 y p) * (weightSlope y : ℂ))
    (fun p y => y ^ 2 * rsZeroMoment 1 (Real.log y) p * |weightSlope y|)
    (fun p => (zeroPrimitive_slope_integrable p hx).aestronglyMeasurable)
    (fun p => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact zeroPrimitive_slope_norm_bound p (hx.trans hy))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact ((rsZeroMoment_summable (by omega : 1 ≤ 1)
        (Real.log_nonneg (hx.trans hy).le)).mul_left (y ^ 2)).mul_right _)
    (by
      simp_rw [tsum_mul_right, tsum_mul_left]
      exact zeroSlopeEnvelope_integrableOn hx)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (rsZeroPrimitive_summable (by omega : 1 ≤ 1) (hx.trans hy).le).hasSum.mul_right _)
  exact h.tsum_eq.symm

theorem actual_infinite_weighted_spectral_identity {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, signedPsiError y) =
      -spectralPrimitive x * weight x -
        (∑' p, ∫ y in Ioi x, rsZeroPrimitive 1 y p * (weightSlope y : ℂ)).re +
          ∫ y in Ioi x, signedCorrection y := by
  have hr := Complex.reCLM.integral_comp_comm (zeroSum_slope_integrable hx)
  have hi : IntegrableOn (fun y => spectralPrimitive y * weightSlope y) (Ioi x) := by
    apply (zeroSum_slope_integrable hx).re.congr
    filter_upwards with y
    simp [spectralPrimitive]
  have he := tendsto_nhds_unique (actual_spectral_weighted_tail_limit hx)
    (intervalIntegral_tendsto_integral_Ioi x hi tendsto_id)
  have hreal : (∫ y in Ioi x, spectralPrimitive y * weightSlope y) =
      (∑' p, ∫ y in Ioi x, rsZeroPrimitive 1 y p * (weightSlope y : ℂ)).re := by
    rw [← zeroSum_slope_integral_exchange hx]
    convert! hr using 1
    congr 1
    ext y
    simp [spectralPrimitive, Complex.mul_re]
  rw [hreal] at he
  linarith

#print axioms zeroSum_slope_integral_exchange
#print axioms actual_infinite_weighted_spectral_identity

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
