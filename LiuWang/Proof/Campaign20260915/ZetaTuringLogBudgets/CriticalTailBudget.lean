import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalC2Witness
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SourceLocalBudgets
import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.OriginalScale
import LiuWang.Proof.Campaign20260915.ZetaC2RightTail.SourceError
import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelPhiBounds

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem sourceCentralNormalized_original_tail {eta : ℝ}
    (he : 49 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| ≤ 7 / 4 := by
  have he0 : 0 < eta := by linarith
  let H := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel (criticalPoint (sourceTime eta)) ⌊eta⌋₊ (rsDescentPoint eta y)
  let P := rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
    (sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ))
  have hb := LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_one_sharp_R0
    he0.le (by nlinarith : 125 < eta ^ 2) hint
  rw [source_criticalPoint] at hb
  change ‖H - P‖ ≤ eta ^ (-(1 / 2 : ℝ)) * ((37 / 50) / eta) at hb
  have hphi := rsPhi_uniform_bound (sourcePhiParameter_mem
    (Nat.zero_le_self_sub_floor he0.le) (Nat.self_sub_floor_lt_one eta).le)
  have hphase : ‖sourceGaussianPhase eta ⌊eta⌋₊‖ = 1 := by
    rw [sourceGaussianPhase, norm_exp]
    simp [mul_re, mul_im, pow_two]
  have hP : ‖P‖ ≤ eta ^ (-(1 / 2 : ℝ)) * 12 := by
    dsimp only [P]
    rw [norm_mul, norm_mul, hphase, one_mul, norm_real, Real.norm_eq_abs,
      exterior_localPrefactor_norm (1 / 2) he0, abs_of_pos hphi.1]
    norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left hphi.2 (Real.rpow_nonneg he0.le _)
  have hroot : 7 ≤ Real.sqrt eta := by
    nlinarith [Real.sq_sqrt he0.le, Real.sqrt_nonneg eta]
  have hpow : eta ^ (-(1 / 2 : ℝ)) ≤ 1 / 7 := by
    rw [Real.rpow_neg he0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hroot
  have hsmall : (37 / 50 : ℝ) / eta ≤ 1 / 4 := by
    rw [div_le_iff₀ he0]
    linarith
  have hH : ‖H‖ ≤ 7 / 4 := by
    have hn := norm_add_le (H - P) P
    rw [sub_add_cancel] at hn
    have hsum : 12 + (37 / 50 : ℝ) / eta ≤ 12 + 1 / 4 := by linarith
    have hprod := mul_le_mul hpow hsum
      (by positivity : 0 ≤ 12 + (37 / 50 : ℝ) / eta) (by norm_num : (0 : ℝ) ≤ 1 / 7)
    nlinarith
  exact (hankel_normalized_re_bound (sourceTime_pos he0) H).trans hH

theorem sourceLeftNormalized_original_tail {eta : ℝ} (he : 49 ≤ eta) :
    |sourceLeftNormalized eta| ≤ 1 / 10 := by
  have ht : (criticalPoint (sourceTime eta)).im = 2 * Real.pi * eta ^ 2 := by
    simp only [criticalPoint, sourceTime, mul_pow, rsSaddleScale_sq]
  have hb := LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_hankel_floor_budget
    (by linarith : 10 ≤ eta)
    (by norm_num [criticalPoint] : (criticalPoint (sourceTime eta)).re = 1 / 2) ht
  have hphi := abs_re_le_norm
    (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
      (∫ r : ℝ in Set.Ioi 0,
        rsC2LeftIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ r) *
      criticalGammaPhase (sourceTime eta))
  rw [norm_mul, norm_criticalGammaPhase, mul_one] at hphi
  apply (hphi.trans hb).trans
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 1 ≤ eta) 4
  norm_num at hp
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

theorem sourceRightNormalized_original_tail {eta : ℝ} (he : 49 ≤ eta) :
    |sourceRightNormalized eta| ≤ 1 / 10 := by
  have he0 : 0 < eta := by linarith
  have hb := LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactored_right_tail_effective
    (by linarith : 1 ≤ eta) (Nat.lt_floor_add_one eta).le
  rw [source_criticalPoint] at hb
  have hphi := abs_re_le_norm
    (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
      (∫ y : ℝ in Set.Ioi (eta / 2),
        rsC2RightIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ y) *
      criticalGammaPhase (sourceTime eta))
  rw [norm_mul, norm_criticalGammaPhase, mul_one] at hphi
  apply (hphi.trans hb).trans
  have hpow : eta ^ (-(3 / 2 : ℝ)) ≤ 1 / eta := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ eta)
      (by norm_num : -(3 / 2 : ℝ) ≤ -1)
    simpa only [Real.rpow_neg_one, one_div] using h
  have hpi : (11 : ℝ) / (2 * Real.pi) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hexp : Real.exp (-((rsSaddleScale * eta) ^ 2) / 11) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (rsSaddleScale * eta)])
  have hm := mul_le_mul hpi hpow (Real.rpow_nonneg he0.le _) (by norm_num : (0 : ℝ) ≤ 2)
  have hall := mul_le_mul hm hexp (Real.exp_pos _).le (by positivity : 0 ≤ 2 * (1 / eta))
  apply hall.trans
  rw [mul_one, mul_one_div, div_le_iff₀ he0]
  linarith

theorem sourceC2_mass_original_tail {eta : ℝ}
    (he : 49 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
      |sourceRightNormalized eta| ≤ 39 / 20 := by
  linarith [sourceCentralNormalized_original_tail he hint,
    sourceLeftNormalized_original_tail he, sourceRightNormalized_original_tail he]

theorem norm_zeta_original_growth_tail {eta : ℝ}
    (he : 49 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖riemannZeta (criticalPoint (sourceTime eta))‖ ≤
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) - 1 / 20 := by
  have h := norm_zeta_original_C2_growth_budget (by linarith : 8 ≤ eta) hint
  linarith [sourceC2_mass_original_tail he hint]

theorem criticalGrowth_bounded_C2_witness {t : ℝ} (ht : 128 * Real.pi ≤ t)
    (hbad : (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖) :
    ∃ eta : ℝ, eta ∈ Set.Ioo 8 49 ∧ (∀ k : ℤ, eta ≠ k) ∧
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) <
        ‖riemannZeta (criticalPoint (sourceTime eta))‖ ∧
      2 < |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
        |sourceRightNormalized eta| := by
  obtain ⟨eta, he, hint, hz⟩ := criticalGrowth_noninteger_witness ht hbad
  have he49 : eta < 49 := by
    by_contra h
    have hg := norm_zeta_original_growth_tail (not_lt.mp h) hint
    linarith
  refine ⟨eta, ⟨he, he49⟩, hint, hz, ?_⟩
  linarith [norm_zeta_original_C2_growth_budget he.le hint]

theorem horizontalLogMass_bounded_C2_witness {T : ℝ} (hT : 128 * Real.pi ≤ T)
    (hbad : sourceHorizontalLogBudget T <
      LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass T) :
    ∃ eta : ℝ, eta ∈ Set.Ioo 8 49 ∧ (∀ k : ℤ, eta ≠ k) ∧
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) <
        ‖riemannZeta (criticalPoint (sourceTime eta))‖ ∧
      2 < |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
        |sourceRightNormalized eta| := by
  obtain ⟨t, ht, h⟩ := horizontalLogMass_violation_critical_witness hT hbad
  exact criticalGrowth_bounded_C2_witness ht h

#print axioms sourceCentralNormalized_original_tail
#print axioms sourceC2_mass_original_tail
#print axioms norm_zeta_original_growth_tail
#print axioms criticalGrowth_bounded_C2_witness
#print axioms horizontalLogMass_bounded_C2_witness

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
