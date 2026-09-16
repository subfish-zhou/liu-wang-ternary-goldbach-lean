import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalTailBudget
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ExactLogMassBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem sinc_half_pi_lower {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    2 / Real.pi ≤ Real.sinc x := by
  have hp (y : ℝ) (hy : 0 < y) (hb : y ≤ Real.pi / 2) :
      2 / Real.pi ≤ Real.sinc y := by
    rw [Real.sinc_of_ne_zero hy.ne', le_div_iff₀ hy]
    exact Real.mul_le_sin hy.le hb
  rcases lt_trichotomy x 0 with hn | rfl | hp0
  · rw [← Real.sinc_neg]
    exact hp (-x) (by linarith) (by rwa [abs_of_neg hn] at hx)
  · rw [Real.sinc_zero, div_le_one Real.pi_pos]
    exact Real.two_le_pi
  · exact hp x hp0 (by rwa [abs_of_pos hp0] at hx)

theorem critical_phi_budget {z : ℝ} (hz : |z| ≤ 1) :
    0 < rsPhi z ∧ rsPhi z ≤ 3 := by
  have hpos (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : rsPhi x ≤ 3 := by
    have hb := rs_sinc_lower (x := Real.pi / 2 * (x + 1 / 2)) (by
      rw [abs_le]
      constructor <;> nlinarith [Real.pi_pos])
    have hs := sinc_half_pi_lower (x := Real.pi / 2 * (x - 1 / 2)) (by
      rw [abs_le]
      constructor <;> nlinarith [Real.pi_pos])
    have hprod := mul_le_mul hb hs (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
      (by linarith : 0 ≤ Real.sinc (Real.pi / 2 * (x + 1 / 2)))
    have hd : 1 / 3 ≤ Real.pi *
        (Real.sinc (Real.pi / 2 * (x + 1 / 2)) *
          Real.sinc (Real.pi / 2 * (x - 1 / 2))) := by
      calc
        _ = Real.pi * ((1 / 6 : ℝ) * (2 / Real.pi)) := by field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod Real.pi_pos.le
    rw [rsPhi, div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hd)]
    linarith [Real.sinc_le_one (Real.pi / 2 * (x ^ 2 - 1 / 4))]
  refine ⟨(rsPhi_uniform_bound hz).1, ?_⟩
  rcases le_total 0 z with h | h
  · exact hpos z h (abs_le.mp hz).2
  · have hh := hpos (-z) (by linarith) (by linarith [(abs_le.mp hz).1])
    rwa [rsPhi_even] at hh

theorem sourceCentralNormalized_medium_growth {eta : ℝ}
    (he : 11 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| ≤ 5 / 4 := by
  have he0 : 0 < eta := by linarith
  let H := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel (criticalPoint (sourceTime eta)) ⌊eta⌋₊ (rsDescentPoint eta y)
  let P := rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
    (sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ))
  have hb := LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_one_sharp_error he hint
  rw [source_criticalPoint] at hb
  have ho := LiuWang.Proof.Campaign20260915.ZetaJnCentral.one_polynomial_outer_allocation he
  have herr : ‖H - P‖ ≤ eta ^ (-(1 / 2 : ℝ)) * ((37 / 50) / eta) := by
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg he0.le _)
    exact (add_le_add le_rfl ho).trans_eq (by ring)
  have hphi := critical_phi_budget (sourcePhiParameter_mem
    (Nat.zero_le_self_sub_floor he0.le) (Nat.self_sub_floor_lt_one eta).le)
  have hphase : ‖sourceGaussianPhase eta ⌊eta⌋₊‖ = 1 := by
    rw [sourceGaussianPhase, norm_exp]
    simp [mul_re, mul_im, pow_two]
  have hP : ‖P‖ ≤ eta ^ (-(1 / 2 : ℝ)) * 3 := by
    dsimp only [P]
    rw [norm_mul, norm_mul, hphase, one_mul, norm_real, Real.norm_eq_abs,
      exterior_localPrefactor_norm (1 / 2) he0, abs_of_pos hphi.1]
    norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left hphi.2 (Real.rpow_nonneg he0.le _)
  have hroot : 3 ≤ Real.sqrt eta := by
    nlinarith [Real.sq_sqrt he0.le, Real.sqrt_nonneg eta]
  have hpow : eta ^ (-(1 / 2 : ℝ)) ≤ 1 / 3 := by
    rw [Real.rpow_neg he0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hroot
  have hsum : 3 + (37 / 50 : ℝ) / eta ≤ 3 + 3 / 4 := by
    have hsmall : (37 / 50 : ℝ) / eta ≤ 3 / 4 := by
      rw [div_le_iff₀ he0]
      linarith
    linarith
  have hprod := mul_le_mul hpow hsum
    (by positivity : 0 ≤ 3 + (37 / 50 : ℝ) / eta) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hn := norm_add_le (H - P) P
  rw [sub_add_cancel] at hn
  exact (hankel_normalized_re_bound (sourceTime_pos he0) H).trans (by nlinarith)

theorem sourceC2_nonlocal_medium_growth {eta : ℝ} (he : 11 ≤ eta) :
    |sourceLeftNormalized eta| + |sourceRightNormalized eta| ≤ 3 / 10 := by
  have he0 : 0 < eta := by linarith
  have ht : (criticalPoint (sourceTime eta)).im = 2 * Real.pi * eta ^ 2 := by
    simp only [criticalPoint, sourceTime, mul_pow, rsSaddleScale_sq]
  have hleft := LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_hankel_floor_budget
    (by linarith : 10 ≤ eta)
    (by norm_num [criticalPoint] : (criticalPoint (sourceTime eta)).re = 1 / 2) ht
  have hright := LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactored_right_tail_effective
    (by linarith : 1 ≤ eta) (Nat.lt_floor_add_one eta).le
  rw [source_criticalPoint] at hright
  have hL : |sourceLeftNormalized eta| ≤ 1 / 10 := by
    apply (abs_re_le_norm _).trans
    rw [norm_mul, norm_criticalGammaPhase, mul_one]
    apply hleft.trans
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 1 ≤ eta) 4
    norm_num at hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hR : |sourceRightNormalized eta| ≤ 1 / 5 := by
    apply (abs_re_le_norm _).trans
    rw [norm_mul, norm_criticalGammaPhase, mul_one]
    apply hright.trans
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
  linarith

theorem norm_zeta_original_medium_growth {eta : ℝ}
    (he : 11 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖riemannZeta (criticalPoint (sourceTime eta))‖ ≤
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) - 9 / 20 := by
  have h := norm_zeta_original_C2_growth_budget (by linarith : 8 ≤ eta) hint
  linarith [sourceCentralNormalized_medium_growth he hint, sourceC2_nonlocal_medium_growth he]

theorem criticalGrowth_small_window_witness {t : ℝ} (ht : 128 * Real.pi ≤ t)
    (hbad : (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖) :
    ∃ eta : ℝ, eta ∈ Set.Ioo 8 11 ∧ (∀ k : ℤ, eta ≠ k) ∧
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) <
        ‖riemannZeta (criticalPoint (sourceTime eta))‖ ∧
      2 < |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
        |sourceRightNormalized eta| := by
  obtain ⟨eta, he, hint, hz, hC2⟩ := criticalGrowth_bounded_C2_witness ht hbad
  have he11 : eta < 11 := by
    by_contra h
    have hg := norm_zeta_original_medium_growth (not_lt.mp h) hint
    linarith
  exact ⟨eta, ⟨he.1, he11⟩, hint, hz, hC2⟩

theorem horizontalLogMass_exact_small_window_witness {T : ℝ} (hT : 128 * Real.pi ≤ T)
    (hbad : sourceExactHorizontalLogBudget T <
      LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass T) :
    ∃ eta : ℝ, eta ∈ Set.Ioo 8 11 ∧ (∀ k : ℤ, eta ≠ k) ∧
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) <
        ‖riemannZeta (criticalPoint (sourceTime eta))‖ ∧
      2 < |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
        |sourceRightNormalized eta| := by
  have ht : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hu := horizontalLogMass_real_tail_upper ht.ne' (by norm_num : (1 : ℝ) < 5 / 4)
  have hI :
      (∫ x in (1 / 2 : ℝ)..(5 / 4),
        Real.log (sourceStripNormEnvelope (LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalAt T x))) <
      ∫ x in (1 / 2 : ℝ)..(5 / 4),
        Real.log ‖riemannZeta (LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalAt T x)‖ := by
    unfold sourceExactHorizontalLogBudget at hbad
    linarith
  obtain ⟨t, ht, h⟩ := sourceStrip_integral_violation_critical_witness hT hI
  exact criticalGrowth_small_window_witness ht h

#print axioms critical_phi_budget
#print axioms sourceCentralNormalized_medium_growth
#print axioms norm_zeta_original_medium_growth
#print axioms criticalGrowth_small_window_witness
#print axioms horizontalLogMass_exact_small_window_witness

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
