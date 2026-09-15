import LiuWang.Proof.Campaign20260915.Totient.RSCountImproper

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_log_quot_pos {t : ℝ} (ht : rsA ≤ t) :
    0 < Real.log (t / (2 * Real.pi)) := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith [rsA_ge_thousand, Real.pi_lt_four]

theorem rsQ_split {t : ℝ} (ht : rsA ≤ t) :
    rsQ t = 1 / (2 * Real.pi) + 0.137 / (t * Real.log (t / (2 * Real.pi))) +
      0.443 / (t * Real.log t * Real.log (t / (2 * Real.pi))) := by
  have ht0 : 0 < t := by linarith [rsA_ge_thousand]
  have hl : 0 < Real.log t := Real.log_pos (by linarith [rsA_ge_thousand])
  have hq := rs_log_quot_pos ht
  unfold rsQ
  field_simp
  ring

theorem rsQ_pos {t : ℝ} (ht : rsA ≤ t) : 0 < rsQ t := by
  have ht0 : 0 < t := by linarith [rsA_ge_thousand]
  have hl : 0 < Real.log t := Real.log_pos (by linarith [rsA_ge_thousand])
  have hq := rs_log_quot_pos ht
  rw [rsQ_split ht]
  positivity

theorem rsQ_strictAntiOn : StrictAntiOn rsQ (Ici rsA) := by
  intro a ha b hb hab
  change rsA ≤ a at ha
  change rsA ≤ b at hb
  have ha0 : 0 < a := by linarith [rsA_ge_thousand]
  have hb0 : 0 < b := ha0.trans hab
  have hal : 0 < Real.log a := Real.log_pos (by linarith [rsA_ge_thousand])
  have hbl : 0 < Real.log b := Real.log_pos (by linarith [rsA_ge_thousand])
  have haq := rs_log_quot_pos ha
  have hbq := rs_log_quot_pos hb
  have hl := Real.log_le_log ha0 hab.le
  have hq := Real.log_le_log (by positivity : 0 < a / (2 * Real.pi))
    (div_le_div_of_nonneg_right hab.le (by positivity))
  rw [rsQ_split ha, rsQ_split hb]
  have hfirst : 0.137 / (b * Real.log (b / (2 * Real.pi))) <
      0.137 / (a * Real.log (a / (2 * Real.pi))) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    exact (mul_lt_mul_of_pos_right hab haq).trans_le
      (mul_le_mul_of_nonneg_left hq hb0.le)
  have hsecond : 0.443 / (b * Real.log b * Real.log (b / (2 * Real.pi))) ≤
      0.443 / (a * Real.log a * Real.log (a / (2 * Real.pi))) := by
    gcongr
  linarith

theorem rsQ_continuousOn : ContinuousOn rsQ (Ici rsA) := by
  intro t ht
  change rsA ≤ t at ht
  have ht0 : t ≠ 0 := (by linarith [rsA_ge_thousand] : 0 < t).ne'
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [rsA_ge_thousand] : 1 < t)).ne'
  have hq : Real.log (t / (2 * Real.pi)) ≠ 0 := (rs_log_quot_pos ht).ne'
  have hc : 2 * Real.pi ≠ 0 := by positivity
  have htc : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht0 hc
  have hd : t * Real.log t * Real.log (t / (2 * Real.pi)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ht0 hl) hq
  apply ContinuousAt.continuousWithinAt
  unfold rsQ
  fun_prop

private theorem log_div_sq_integrable {K : ℝ} (hK : 1 < K) :
    IntegrableOn (fun t : ℝ => Real.log t / t ^ 2) (Ioi K) := by
  have hd (t : ℝ) (ht : t ∈ Ici K) :
      HasDerivAt (fun u => -((Real.log u + 1) / u)) (Real.log t / t ^ 2) t := by
    change K ≤ t at ht
    have ht0 : 0 < t := by linarith
    convert! (((Real.hasDerivAt_log ht0.ne').add_const 1).div
      (hasDerivAt_id t) ht0.ne').neg using 1
    simp only [id_eq]
    field_simp
    ring
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  apply integrableOn_Ioi_deriv_of_nonneg' hd
  · intro t ht
    exact div_nonneg (Real.log_pos (hK.trans ht)).le (sq_nonneg _)
  · simpa only [add_div, add_zero, neg_zero] using (hlog.add hinv).neg

theorem rs_phi_log_integrableOn {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m) :
    IntegrableOn (fun t => rsPhi m L t * Real.log (t / (2 * Real.pi))) (Ioi K) := by
  have hK1 : 1 < K := by linarith [rsA_ge_thousand]
  have hc : ContinuousOn (fun t => rsPhi m L t * Real.log (t / (2 * Real.pi)))
      (Ioi K) := by
    intro t ht
    change K < t at ht
    apply ContinuousAt.continuousWithinAt
    have ht0 : t ≠ 0 := (by linarith : 0 < t).ne'
    have hc : 2 * Real.pi ≠ 0 := by positivity
    have htc : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht0 hc
    exact (rsPhi_hasDerivAt m L (hK1.trans ht)).continuousAt.mul (by fun_prop)
  apply (log_div_sq_integrable hK1).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change K < t at ht
  have ht0 : 0 < t := by linarith
  have htl : 0 < Real.log t := Real.log_pos (hK1.trans ht)
  have htq := rs_log_quot_pos (hK.trans ht.le)
  have hqle : Real.log (t / (2 * Real.pi)) ≤ Real.log t := by
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hp : rsPhi m L t ≤ 1 / t ^ 2 :=
    (rsPhi_le_power m hL (hK1.trans ht)).trans
      (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by linarith) (by omega)))
  rw [Real.norm_of_nonneg (mul_nonneg (rsPhi_pos m L ht0).le htq.le)]
  calc
    _ ≤ (1 / t ^ 2) * Real.log t := mul_le_mul hp hqle htq.le (by positivity)
    _ = _ := by ring

theorem rsQ_phi_density_integrableOn {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m) :
    IntegrableOn (fun t => rsQ t * (rsPhi m L t * Real.log (t / (2 * Real.pi))))
      (Ioi K) := by
  have hi := rs_phi_log_integrableOn hK hL hm
  have hc := rsQ_continuousOn.mono (show Ioi K ⊆ Ici rsA from fun _ ht => hK.trans ht.le)
  apply (hi.const_mul (rsQ K)).mono' (hc.aestronglyMeasurable measurableSet_Ioi |>.mul
    hi.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ha := hK.trans ht.le
  have ht0 : 0 < t := by linarith [rsA_ge_thousand]
  have hn : 0 ≤ rsPhi m L t * Real.log (t / (2 * Real.pi)) :=
    mul_nonneg (rsPhi_pos m L ht0).le (rs_log_quot_pos ha).le
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (rsQ_pos ha).le hn)]
  exact mul_le_mul_of_nonneg_right (rsQ_antitoneOn hK ha ht.le) hn

theorem rsQ_phi_density_strict {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m) :
    (∫ t in Ioi K, rsQ t * (rsPhi m L t * Real.log (t / (2 * Real.pi)))) <
      rsQ K * ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
  let g (t : ℝ) := rsQ K * (rsPhi m L t * Real.log (t / (2 * Real.pi)))
  let f (t : ℝ) := rsQ t * (rsPhi m L t * Real.log (t / (2 * Real.pi)))
  have hg : IntegrableOn g (Ioi K) := (rs_phi_log_integrableOn hK hL hm).const_mul _
  have hf : IntegrableOn f (Ioi K) := rsQ_phi_density_integrableOn hK hL hm
  have hpos (t : ℝ) (ht : t ∈ Ioi K) : 0 < g t - f t := by
    change K < t at ht
    apply sub_pos.mpr
    apply mul_lt_mul_of_pos_right (rsQ_strictAntiOn hK (hK.trans ht.le) ht)
    exact mul_pos (rsPhi_pos m L (by linarith [rsA_ge_thousand]))
      (rs_log_quot_pos (hK.trans ht.le))
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi K)] (fun t => g t - f t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using (hpos t ht).le
  have hs : Function.support (fun t => g t - f t) ∩ Ioi K = Ioi K :=
    inter_eq_right.mpr (fun t ht => (hpos t ht).ne')
  have hp : 0 < ∫ t in Ioi K, g t - f t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnon (hg.sub hf), hs]
    simp
  rw [integral_sub hg hf] at hp
  simpa only [g, f, integral_const_mul] using sub_pos.mp hp

#print axioms rs_log_quot_pos
#print axioms rsQ_split
#print axioms rsQ_pos
#print axioms rsQ_strictAntiOn
#print axioms rsQ_continuousOn
#print axioms rs_phi_log_integrableOn
#print axioms rsQ_phi_density_integrableOn
#print axioms rsQ_phi_density_strict

end LiuWang.Proof.Campaign20260915.Totient
