import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.PsiTransport
import LiuWang.Proof.Campaign20260915.Totient.ThetaDecay

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def signedPsiError (y : ℝ) : ℝ := (y - Chebyshev.psi y) * weight y

theorem signedPsiError_intervalIntegrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable signedPsiError volume a b := by
  have hsub : uIcc a b ⊆ Ioi (1 : ℝ) := by
    rw [uIcc_of_le hab]
    exact fun _ hy => ha.trans_le hy.1
  exact ((continuous_id.intervalIntegrable a b).sub Chebyshev.psi_mono.intervalIntegrable).mul_continuousOn
    (weight_continuousOn.mono hsub)

theorem signedPsiError_tail_norm_bound {y : ℝ} (hy : 0 < y)
    (hlog : 2 * Real.exp 100 ≤ Real.log y) :
    ‖signedPsiError y‖ ≤ 1028 * (y⁻¹ / Real.log y ^ 2) := by
  have hl1 : 1 ≤ Real.log y := le_trans (by norm_num) (log_large_of_tail hlog)
  have hl : 0 < Real.log y := lt_of_lt_of_le zero_lt_one hl1
  have hy1 : 1 < y := (Real.log_pos_iff hy.le).mp hl
  have hpow : Real.log y ≤ Real.log y ^ 3 := by
    simpa using pow_le_pow_right₀ hl1 (by omega : 1 ≤ 3)
  have he := (psi_error_le_log_cube hy hlog).trans
    (div_le_div_of_nonneg_left (by positivity) hl hpow)
  have hw : weight y ≤ 2 / (y ^ 2 * Real.log y) := by
    unfold weight
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (sq_nonneg y) (mul_nonneg hl.le (sub_nonneg.mpr hl1))]
  change |(y - Chebyshev.psi y) * weight y| ≤ _
  rw [abs_mul, abs_sub_comm y, abs_of_nonneg (weight_nonneg hy1)]
  apply (mul_le_mul he hw (weight_nonneg hy1) (by positivity)).trans_eq
  field_simp
  ring

theorem signedPsiError_integrableOn {x : ℝ} (hx : 1 < x) :
    IntegrableOn signedPsiError (Ioi x) := by
  let b := max x (Real.exp (2 * Real.exp 100))
  have hxb : x ≤ b := le_max_left _ _
  have hb : 1 < b := hx.trans_le hxb
  have ht : IntegrableOn signedPsiError (Ioi b) := by
    refine ((integrableOn_inv_div_log_sq_Ioi hb).const_mul 1028).mono'
      (by
        apply Measurable.aestronglyMeasurable
        exact (measurable_id.sub Chebyshev.psi_mono.measurable).mul
          (by unfold weight; fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := lt_trans (lt_trans zero_lt_one hb) hy
    apply signedPsiError_tail_norm_bound hy0
    exact (Real.le_log_iff_exp_le hy0).mpr ((le_max_right _ _).trans hy.le)
  rw [← Ioc_union_Ioi_eq_Ioi hxb]
  exact ((signedPsiError_intervalIntegrable hx hxb).1).union ht

theorem signedPsiError_improper_limit {x : ℝ} (hx : 1 < x) :
    Tendsto (fun b => ∫ y in x..b, signedPsiError y) atTop
      (𝓝 (∫ y in Ioi x, signedPsiError y)) :=
  intervalIntegral_tendsto_integral_Ioi x (signedPsiError_integrableOn hx) tendsto_id

theorem spectralPrimitive_weight_tendsto_zero :
    Tendsto (fun x => spectralPrimitive x * weight x) atTop (𝓝 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp zeroSum_weight_tendsto_zero
  simpa [Function.comp_def, spectralPrimitive, Complex.mul_re] using h

theorem actual_spectral_weighted_tail_limit {x : ℝ} (hx : 1 < x) :
    Tendsto (fun b => ∫ y in x..b, spectralPrimitive y * weightSlope y) atTop
      (𝓝 (-spectralPrimitive x * weight x +
        (∫ y in Ioi x, signedCorrection y) - ∫ y in Ioi x, signedPsiError y)) := by
  have hc := intervalIntegral_tendsto_integral_Ioi x
    (signedCorrection_integrable hx) tendsto_id
  have h := ((spectralPrimitive_weight_tendsto_zero.sub_const
    (spectralPrimitive x * weight x)).add hc).sub (signedPsiError_improper_limit hx)
  simp only [zero_sub] at h
  rw [neg_mul]
  apply h.congr'
  filter_upwards [eventually_ge_atTop x] with b hb
  have he := actual_weighted_spectral_compact hx hb
  change (∫ y in x..b, signedPsiError y) =
    weightedPrimitive x b spectralPrimitive + ∫ y in x..b, signedCorrection y at he
  dsimp [weightedPrimitive] at he
  simp only [id_eq]
  linarith

#print axioms signedPsiError_integrableOn
#print axioms actual_spectral_weighted_tail_limit

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
