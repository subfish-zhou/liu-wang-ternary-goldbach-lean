import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalLowLeft

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem critical_inverse_sqrt_scale {eta : ℝ} (he : 8 ≤ eta) :
    eta ^ (-(1 / 2 : ℝ)) ≤ 3 / 8 := by
  have he0 : 0 < eta := by linarith
  have hs : 8 / 3 ≤ Real.sqrt eta := by
    nlinarith [Real.sq_sqrt he0.le, Real.sqrt_nonneg eta]
  rw [Real.rpow_neg he0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8 / 3) hs).trans_eq (by norm_num)

theorem critical_central_original_budget {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| ≤ 7 / 4 := by
  have he0 : 0 < eta := by linarith
  let H := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel (criticalPoint (sourceTime eta)) ⌊eta⌋₊ (rsDescentPoint eta y)
  let A := sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ)
  let J := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y
  let P := rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ * (A + J)
  have hb := exterior_localHankel_one (1 / 2) (by linarith : 1 ≤ eta) hint
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hb
  rw [source_criticalPoint] at hb
  change ‖H - P‖ ≤ eta ^ (-(1 / 2 : ℝ)) *
    (4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4)) at hb
  have hphi := critical_phi_budget (sourcePhiParameter_mem
    (Nat.zero_le_self_sub_floor he0.le) (Nat.self_sub_floor_lt_one eta).le)
  have hphase : ‖sourceGaussianPhase eta ⌊eta⌋₊‖ = 1 := by
    rw [sourceGaussianPhase, norm_exp]
    simp [mul_re, mul_im, pow_two]
  have hA : ‖A‖ ≤ 3 := by
    dsimp only [A]
    rw [norm_mul, hphase, one_mul, norm_real, Real.norm_eq_abs, abs_of_pos hphi.1]
    exact hphi.2
  have hJ : ‖J‖ ≤ 3 / 2 := critical_floor_J1_growth_budget he
  have hP : ‖P‖ ≤ eta ^ (-(1 / 2 : ℝ)) * (9 / 2) := by
    dsimp only [P]
    rw [norm_mul, exterior_localPrefactor_norm (1 / 2) he0]
    norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg he0.le _)
    linarith [norm_add_le A J]
  have hfrac : (4 : ℝ) / (Real.pi * eta) ≤ 1 / 6 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hexp : Real.exp (-Real.pi * eta ^ 2 / 4) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg eta)])
  have houter : 4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4) ≤ 1 / 6 :=
    (mul_le_mul hfrac hexp (Real.exp_pos _).le (by norm_num)).trans_eq (by norm_num)
  have herr := hb.trans (mul_le_mul_of_nonneg_left houter (Real.rpow_nonneg he0.le _))
  have hscale := mul_le_mul_of_nonneg_right (critical_inverse_sqrt_scale he)
    (by norm_num : (0 : ℝ) ≤ 9 / 2 + 1 / 6)
  have hn := norm_add_le (H - P) P
  rw [sub_add_cancel] at hn
  exact (hankel_normalized_re_bound (sourceTime_pos he0) H).trans (by nlinarith)

theorem critical_right_original_budget {eta : ℝ} (he : 8 ≤ eta) :
    |sourceRightNormalized eta| ≤ 1 / 10 := by
  have he0 : 0 < eta := by linarith
  have hb := LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactored_right_tail_effective
    (by linarith : 1 ≤ eta) (Nat.lt_floor_add_one eta).le
  rw [source_criticalPoint] at hb
  apply (abs_re_le_norm _).trans
  rw [norm_mul, norm_criticalGammaPhase, mul_one]
  apply hb.trans
  have hpow : eta ^ (-(3 / 2 : ℝ)) ≤ 3 / 64 := by
    rw [show -(3 / 2 : ℝ) = -(1 / 2 : ℝ) - 1 by norm_num,
      Real.rpow_sub he0, Real.rpow_one]
    exact (div_le_div₀ (by positivity) (critical_inverse_sqrt_scale he)
      (by norm_num : (0 : ℝ) < 8) he).trans_eq (by norm_num)
  have hpi : (11 : ℝ) / (2 * Real.pi) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hexp : Real.exp (-((rsSaddleScale * eta) ^ 2) / 11) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (rsSaddleScale * eta)])
  have hm := mul_le_mul hpi hpow (Real.rpow_nonneg he0.le _) (by norm_num : (0 : ℝ) ≤ 2)
  exact (mul_le_mul hm hexp (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2 * (3 / 64))).trans
    (by norm_num)

theorem critical_C2_original_budget {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
      |sourceRightNormalized eta| ≤ 39 / 20 := by
  linarith [critical_central_original_budget he hint,
    critical_left_normalized_budget he, critical_right_original_budget he]

theorem original_critical_growth {t : ℝ} (ht : 128 * Real.pi ≤ t) :
    ‖riemannZeta (criticalPoint t)‖ ≤ (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) := by
  by_contra h
  obtain ⟨eta, he, hint, _, hC2⟩ := criticalGrowth_small_window_witness ht (not_le.mp h)
  linarith [critical_C2_original_budget he.1.le hint]

theorem sourceHalfStripQuotient_original_bound {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 128 * Real.pi ≤ s.im) :
    ‖sourceHalfStripQuotient s‖ ≤ 1 := by
  by_contra h
  obtain ⟨t, ht, hbad⟩ := sourceHalfStrip_violation_critical_witness hs ht (not_le.mp h)
  linarith [original_critical_growth ht]

theorem sourceStrip_zeta_original_bound {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 128 * Real.pi ≤ s.im) :
    ‖riemannZeta s‖ ≤ sourceStripNormEnvelope s := by
  by_contra h
  obtain ⟨t, ht, hbad⟩ := sourceStrip_norm_violation_critical_witness hs ht (not_le.mp h)
  linarith [original_critical_growth ht]

theorem sourceStrip_log_zeta_original_bound {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 128 * Real.pi ≤ s.im) :
    Real.log ‖riemannZeta s‖ ≤ Real.log (sourceStripNormEnvelope s) := by
  by_contra h
  obtain ⟨t, ht, hbad⟩ := sourceStrip_log_violation_critical_witness hs ht (not_le.mp h)
  linarith [original_critical_growth ht]

theorem sourceStrip_integral_zeta_original_bound {T : ℝ} (hT : 128 * Real.pi ≤ T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), Real.log ‖riemannZeta (horizontalAt T x)‖) ≤
      ∫ x in (1 / 2 : ℝ)..(5 / 4), Real.log (sourceStripNormEnvelope (horizontalAt T x)) := by
  by_contra h
  obtain ⟨t, ht, hbad⟩ := sourceStrip_integral_violation_critical_witness hT (not_le.mp h)
  linarith [original_critical_growth ht]

theorem horizontalLogMass_exact_original_upper {T : ℝ} (hT : 128 * Real.pi ≤ T) :
    horizontalLogMass T ≤ sourceExactHorizontalLogBudget T := by
  have ht : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hu := horizontalLogMass_real_tail_upper ht.ne' (by norm_num : (1 : ℝ) < 5 / 4)
  unfold sourceExactHorizontalLogBudget
  linarith [sourceStrip_integral_zeta_original_bound hT]

#print axioms critical_C2_original_budget
#print axioms original_critical_growth
#print axioms sourceHalfStripQuotient_original_bound
#print axioms sourceStrip_zeta_original_bound
#print axioms sourceStrip_log_zeta_original_bound
#print axioms sourceStrip_integral_zeta_original_bound
#print axioms horizontalLogMass_exact_original_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
