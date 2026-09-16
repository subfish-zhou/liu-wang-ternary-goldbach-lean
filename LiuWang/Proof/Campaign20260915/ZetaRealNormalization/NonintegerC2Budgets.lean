import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.OriginalScaleBudgets
import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelPhiBounds

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaJnCentral

theorem normalized_central_one_sharp {eta : ℝ}
    (he : 11 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta -
      sourceSignedAmplitude eta ⌊eta⌋₊ * (sourcePhaseTransport eta).re *
        rsPhi (sourcePhiParameter eta ⌊eta⌋₊)| ≤
      eta ^ (-(1 / 2 : ℝ)) * ((37 / 50) / eta) := by
  have he0 : 0 < eta := by linarith
  have hb := local_hankel_one_sharp_error he hint
  rw [source_criticalPoint] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (one_polynomial_outer_allocation he)) (Real.rpow_nonneg he0.le _))
  have hc := (hankel_normalized_re_bound (sourceTime_pos he0) _).trans hb'
  have hid :
      rsHankelPrefactor (criticalPoint (sourceTime eta)) *
        (rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
          (sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ))) *
            criticalGammaPhase (sourceTime eta) =
      (sourceSignedAmplitude eta ⌊eta⌋₊ : ℂ) * sourcePhaseTransport eta *
        (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ) := by
    rw [← normalized_source_prefactor he0]
    ring
  have hr : ((sourceSignedAmplitude eta ⌊eta⌋₊ : ℂ) * sourcePhaseTransport eta *
      (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ)).re =
    sourceSignedAmplitude eta ⌊eta⌋₊ * (sourcePhaseTransport eta).re *
      rsPhi (sourcePhiParameter eta ⌊eta⌋₊) := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, mul_zero, sub_zero]
  simp only [mul_sub, sub_mul, sub_re, hid, hr] at hc
  change |sourceCentralNormalized eta - _| ≤ _ at hc
  exact hc.trans_eq (by ring)

theorem original_zero_phase_allocation {eta : ℝ} (he : 11 ≤ eta)
    {z : ℝ} (hz : |z| ≤ 1) (m : ℕ) :
    |sourceSignedAmplitude eta m * (sourcePhaseTransport eta).re * rsPhi z -
      sourceSignedAmplitude eta m * rsPhi z| ≤
        (1 / 100) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have he0 : 0 < eta := by linarith
  have hp : |rsPhi z| ≤ 12 := by
    rw [abs_of_pos (rsPhi_uniform_bound hz).1]
    exact (rsPhi_uniform_bound hz).2
  have hd := (sourcePhaseTransport_re_bound he0).trans (source_real_phase_scalar he0)
  have hs : 12 ≤ eta ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) he 3
    norm_num at h
    linarith
  have hsmall : 1 / (100 * eta ^ 4) * 12 ≤ (1 / 100) / eta := by
    apply (le_div_iff₀ he0).mpr
    field_simp
    nlinarith [mul_nonneg he0.le (show 0 ≤ eta ^ 3 - 12 by linarith)]
  rw [show sourceSignedAmplitude eta m * (sourcePhaseTransport eta).re * rsPhi z -
      sourceSignedAmplitude eta m * rsPhi z =
    sourceSignedAmplitude eta m * ((sourcePhaseTransport eta).re - 1) * rsPhi z by ring,
    abs_mul, abs_mul, abs_sourceSignedAmplitude he0.le, original_scale_zero he0]
  calc
    _ ≤ eta ^ (-(1 / 2 : ℝ)) * (1 / (100 * eta ^ 4) * 12) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hd hp (abs_nonneg _) (by positivity)) (Real.rpow_nonneg he0.le _)
    _ ≤ eta ^ (-(1 / 2 : ℝ)) * ((1 / 100) / eta) :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg he0.le _)
    _ = _ := by ring

theorem normalized_central_zero_margin {eta : ℝ}
    (he : 11 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta -
      sourceSignedAmplitude eta ⌊eta⌋₊ * rsPhi (sourcePhiParameter eta ⌊eta⌋₊)| ≤
        (3 / 4) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have he0 : 0 < eta := by linarith
  have hf := sourceFraction_floor he0.le hint
  have hz := sourcePhiParameter_mem hf.1.le hf.2.le
  have h := (abs_sub_le (sourceCentralNormalized eta)
    (sourceSignedAmplitude eta ⌊eta⌋₊ * (sourcePhaseTransport eta).re *
      rsPhi (sourcePhiParameter eta ⌊eta⌋₊))
    (sourceSignedAmplitude eta ⌊eta⌋₊ * rsPhi (sourcePhiParameter eta ⌊eta⌋₊))).trans
      (add_le_add (normalized_central_one_sharp he hint)
        (original_zero_phase_allocation he hz ⌊eta⌋₊))
  apply h.trans_eq
  rw [original_scale_zero he0]
  ring

theorem normalized_zeta_R0_margin {eta : ℝ}
    (he : 11 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ * rsPhi (sourcePhiParameter eta ⌊eta⌋₊))| ≤
          (19 / 20) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  rw [normalized_zeta_C2_exact (Nat.floor_pos.mpr (by linarith)) hf.1 hf.2]
  have hid (S C A L R : ℝ) : S + C + L - R - (S + A) = (C - A) + L - R := by ring
  rw [hid]
  exact ((abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (normalized_central_zero_margin he hint)
      (original_left_zero he))) (original_right_zero he))).trans_eq (by ring)

theorem normalized_zeta_R0_strict {eta : ℝ}
    (he : 0 ≤ eta) (ht : 125 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ * rsPhi (sourcePhiParameter eta ⌊eta⌋₊))| <
          (3 / 2) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have hp : 0 < (eta ^ 2) ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  exact (normalized_zeta_R0_margin (by nlinarith) hint).trans_lt (by nlinarith)

theorem normalized_central_seven_sharp {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta - sourceSevenNormalized eta ⌊eta⌋₊| ≤
      (103 / 100) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have he0 : 0 < eta := by nlinarith
  have hf := sourceFraction_floor he hint
  have hb := local_hankel_seven_sharp_R2 he ht hint
  rw [source_criticalPoint, ← sourceLocalPolynomial_integral (1 / 2) hf.1 hf.2 7] at hb
  have hc := (hankel_normalized_re_bound (sourceTime_pos he0) _).trans hb
  simp only [mul_sub, sub_mul, sub_re] at hc
  simp only [← mul_assoc] at hc
  change |sourceCentralNormalized eta - sourceSevenNormalized eta ⌊eta⌋₊| ≤ _ at hc
  exact hc.trans_eq (by rw [original_scale_two he0]; ring)

theorem normalized_zeta_full_seven_margin {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourceSevenNormalized eta ⌊eta⌋₊)| ≤
        (123 / 100) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have hf := sourceFraction_floor he hint
  rw [normalized_zeta_C2_exact (Nat.floor_pos.mpr (by nlinarith)) hf.1 hf.2]
  have hid (S C A L R : ℝ) : S + C + L - R - (S + A) = (C - A) + L - R := by ring
  rw [hid]
  exact ((abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (normalized_central_seven_sharp he ht hint)
      (original_left_two he ht))) (original_right_two he ht))).trans_eq (by ring)

theorem normalized_zeta_R2_remaining_correction {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ *
          sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))| ≤
      (123 / 100) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) +
        eta ^ (-(1 / 2 : ℝ)) *
          sourceSevenUniformBudget eta (sourcePhiParameter eta ⌊eta⌋₊) := by
  have hf := sourceFraction_floor he hint
  have h := abs_sub_le (normalizedCriticalZeta (sourceTime eta))
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourceSevenNormalized eta ⌊eta⌋₊)
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourceSignedAmplitude eta ⌊eta⌋₊ *
      sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))
  rw [add_sub_add_left_eq_sub] at h
  exact h.trans (add_le_add (normalized_zeta_full_seven_margin he ht hint)
    (normalized_source_seven_uniform_budget hf.1 hf.2))

#print axioms normalized_zeta_R0_margin
#print axioms normalized_zeta_R0_strict
#print axioms normalized_zeta_full_seven_margin
#print axioms normalized_zeta_R2_remaining_correction

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
