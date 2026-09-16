import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.CriticalAmplitude
import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.CriticalC2Tails

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem critical_polynomial_outer_scalar {eta : ℝ} (he : 8 ≤ eta) :
    4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4) ≤ (1 / 100) / eta := by
  have he0 : 0 < eta := by linarith
  apply (mul_le_mul_of_nonneg_left (critical_outer_exponential he)
    (by positivity : 0 ≤ 4 / (Real.pi * eta))).trans
  field_simp
  nlinarith [Real.pi_gt_three]

theorem critical_central_amplitude {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| ≤
      eta ^ (-(1 / 2 : ℝ)) * (4 + (1001 / 100) / eta) := by
  have he0 : 0 < eta := by linarith
  have hf := sourceFraction_floor he0.le hint
  let H := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel (criticalPoint (sourceTime eta)) ⌊eta⌋₊ (rsDescentPoint eta y)
  let F := rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊
  let P := sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ)
  let J := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y
  have hF : ‖F‖ = eta ^ (-(1 / 2 : ℝ)) := by
    simpa only [F, show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] using
      exterior_localPrefactor_norm (1 / 2) he0 ⌊eta⌋₊
  have hG : ‖sourceGaussianPhase eta ⌊eta⌋₊‖ = 1 := by
    rw [sourceGaussianPhase, norm_exp]
    simp [mul_re, mul_im, pow_two]
  have hP : ‖P‖ ≤ 4 := by
    dsimp only [P]
    rw [norm_mul, hG, one_mul, norm_real, Real.norm_eq_abs]
    exact criticalPhi_amplitude (sourcePhiParameter_mem hf.1.le hf.2.le)
  have hJ : ‖J‖ ≤ 10 / eta := critical_first_Jn_all_positive he0 hf.1.le hf.2.le
  have ho : ‖H - F * (P + J)‖ ≤ eta ^ (-(1 / 2 : ℝ)) * ((1 / 100) / eta) := by
    have h := exterior_localHankel_one (1 / 2) (by linarith : 1 ≤ eta) hint
    norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
      ofReal_div, ofReal_one, ofReal_ofNat] at h
    rw [source_criticalPoint] at h
    exact h.trans (mul_le_mul_of_nonneg_left (critical_polynomial_outer_scalar he)
      (Real.rpow_nonneg he0.le _))
  have hsum : ‖F * (P + J)‖ ≤ eta ^ (-(1 / 2 : ℝ)) * (4 + 10 / eta) := by
    rw [norm_mul, hF]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hP hJ))
      (Real.rpow_nonneg he0.le _)
  have hH : ‖H‖ ≤ eta ^ (-(1 / 2 : ℝ)) * (4 + (1001 / 100) / eta) := by
    calc
      _ = ‖(H - F * (P + J)) + F * (P + J)‖ := by rw [sub_add_cancel]
      _ ≤ ‖H - F * (P + J)‖ + ‖F * (P + J)‖ := norm_add_le _ _
      _ ≤ _ := (add_le_add ho hsum).trans_eq (by ring)
  exact (hankel_normalized_re_bound (sourceTime_pos he0) H).trans hH

theorem critical_central_absolute {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| ≤ 19 / 10 := by
  have he0 : 0 < eta := by linarith
  have hs : 14 / 5 ≤ Real.sqrt eta := by
    nlinarith [Real.sqrt_nonneg eta, Real.sq_sqrt he0.le]
  have hp : eta ^ (-(1 / 2 : ℝ)) ≤ 5 / 14 := by
    rw [Real.rpow_neg he0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div,
      div_le_iff₀ (Real.sqrt_pos.mpr he0)]
    linarith
  have hq : (1001 / 100 : ℝ) / eta ≤ 1001 / 800 :=
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 8) he).trans_eq (by norm_num)
  exact (critical_central_amplitude he hint).trans
    ((mul_le_mul hp (by linarith : 4 + (1001 / 100) / eta ≤ 4 + 1001 / 800)
      (by positivity) (by norm_num : (0 : ℝ) ≤ 5 / 14)).trans (by norm_num))

theorem critical_C2_absolute_mass {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
      |sourceRightNormalized eta| ≤ 48 / 25 := by
  linarith [critical_central_absolute he hint, critical_left_absolute he, critical_right_absolute he]

theorem critical_zeta_main_difference {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      sourceRealMainSum (sourceTime eta) ⌊eta⌋₊| ≤ 48 / 25 := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  rw [normalized_zeta_C2_exact (Nat.floor_pos.mpr (by linarith)) hf.1 hf.2,
    show sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourceCentralNormalized eta +
      sourceLeftNormalized eta - sourceRightNormalized eta -
        sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ =
      sourceCentralNormalized eta + sourceLeftNormalized eta - sourceRightNormalized eta by ring]
  exact ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (critical_C2_absolute_mass he hint)

theorem critical_zeta_norm_main_budget {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖riemannZeta (criticalPoint (sourceTime eta))‖ ≤
      |sourceRealMainSum (sourceTime eta) ⌊eta⌋₊| + 48 / 25 := by
  rw [← abs_normalizedCriticalZeta]
  calc
    _ = |(normalizedCriticalZeta (sourceTime eta) -
        sourceRealMainSum (sourceTime eta) ⌊eta⌋₊) +
          sourceRealMainSum (sourceTime eta) ⌊eta⌋₊| := by rw [sub_add_cancel]
    _ ≤ _ := ((abs_add_le _ _).trans
      (add_le_add (critical_zeta_main_difference he hint) le_rfl)).trans_eq (by ring)

#print axioms critical_C2_absolute_mass
#print axioms critical_zeta_main_difference
#print axioms critical_zeta_norm_main_budget

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
