import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceMomentAllocations

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem source_real_correction_amplitude {eta : ℝ} {m : ℕ}
    (he : 1 ≤ eta) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |sourceRealCorrection eta (sourcePhiParameter eta m)| ≤ 6 := by
  have he0 : 0 < eta := by linarith
  have hP0 := criticalPhi_amplitude (sourcePhiParameter_mem h0.le h1.le)
  have hP1 := source_phi_one_amplitude h0 h1
  have hP2 := source_phi_two_amplitude h0 h1
  have hdiv1 : |rsPhiOne (sourcePhiParameter eta m) / eta| ≤ 1 := by
    rw [abs_div, abs_of_pos he0, div_le_iff₀ he0]
    linarith
  have hdiv2 : |rsPhiTwo (sourcePhiParameter eta m) / eta ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_pos (pow_pos he0 2), div_le_iff₀ (pow_pos he0 2)]
    nlinarith
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hP0 hdiv1)) hdiv2)).trans (by norm_num)

theorem source_imaginary_correction_amplitude {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |sourceImaginaryCorrection eta (sourcePhiParameter eta m)| ≤ 1 / (72 * eta ^ 2) := by
  have hp := criticalPhi_amplitude (sourcePhiParameter_mem h0.le h1.le)
  rw [sourceImaginaryCorrection, abs_div, abs_of_pos (by positivity : 0 < 96 * Real.pi * eta ^ 2)]
  apply (div_le_div_of_nonneg_right hp (by positivity)).trans
  field_simp
  nlinarith [Real.pi_gt_three]

theorem source_extra_correction_allocation {eta : ℝ} {m : ℕ}
    (he : 1 ≤ eta) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    sourceExtraBudget eta (sourcePhiParameter eta m) ≤ (9 / 10) / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  obtain ⟨_, _, h3, h4, h5, h6⟩ := source_moments_one_to_six h0 h1
  have hp := Real.pi_lt_four.le
  have hpow (n : ℕ) (hn : 3 ≤ n) : 1 / eta ^ n ≤ 1 / eta ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ he hn)
  have h4' := hpow 4 (by decide)
  have h5' := hpow 5 (by decide)
  have h6' := hpow 6 (by decide)
  calc
    _ ≤ 5 / (16 * eta ^ 3) * (1 / 5) + 35 / (128 * eta ^ 4) * (1 / 10) +
        (9 * 4 / (10 * eta ^ 3) + 63 / (256 * eta ^ 5)) * (1 / 10) +
        (223 * 4 / (240 * eta ^ 4) + 231 / (1024 * eta ^ 6)) * (1 / 10) := by
      unfold sourceExtraBudget
      gcongr
    _ = (1 / 16 + 9 / 25) * (1 / eta ^ 3) +
        (7 / 256 + 223 / 600) * (1 / eta ^ 4) +
        (63 / 2560) * (1 / eta ^ 5) + (231 / 10240) * (1 / eta ^ 6) := by ring
    _ ≤ (1 / 16 + 9 / 25 + 7 / 256 + 223 / 600 + 63 / 2560 + 231 / 10240) *
        (1 / eta ^ 3) := by
      linear_combination (7 / 256 + 223 / 600) * h4' + (63 / 2560) * h5' + (231 / 10240) * h6'
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right
        (show (1 / 16 + 9 / 25 + 7 / 256 + 223 / 600 + 63 / 2560 + 231 / 10240 : ℝ) ≤
          9 / 10 by norm_num) (by positivity : 0 ≤ 1 / eta ^ 3)
      simpa only [mul_one_div] using h

theorem normalized_source_seven_original_allocation {eta : ℝ} {m : ℕ}
    (he : 1 ≤ eta) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |sourceSevenNormalized eta m -
      sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m)| ≤
        eta ^ (-(1 / 2 : ℝ)) * (1 / eta ^ 3) := by
  have he0 : 0 < eta := by linarith
  let A := sourceRealCorrection eta (sourcePhiParameter eta m)
  let b := sourceImaginaryCorrection eta (sourcePhiParameter eta m)
  let E := sourceExtraCorrection eta (sourcePhiParameter eta m)
  let p := sourcePhaseTransport eta
  have hE : |(p * E).re| ≤ (9 / 10) / eta ^ 3 := by
    calc
      _ ≤ ‖p * E‖ := abs_re_le_norm _
      _ ≤ ‖E‖ := by
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (sourcePhaseTransport_norm eta) (norm_nonneg E)
      _ ≤ _ := (sourceExtraCorrection_bound he0 _).trans (source_extra_correction_allocation he h0 h1)
  have hR : |p.re - 1| * |A| ≤ 1 / (100 * eta ^ 4) * 6 :=
    mul_le_mul ((sourcePhaseTransport_re_bound he0).trans (source_real_phase_scalar he0))
      (source_real_correction_amplitude he h0 h1) (abs_nonneg A) (by positivity)
  have hI : |p.im| * |b| ≤ 2 / (25 * eta ^ 2) * (1 / (72 * eta ^ 2)) :=
    mul_le_mul ((sourcePhaseTransport_im_bound he0).trans (source_imaginary_phase_scalar he))
      (source_imaginary_correction_amplitude he0 h0 h1) (abs_nonneg b) (by positivity)
  have hphase : 1 / (100 * eta ^ 4) * 6 +
      2 / (25 * eta ^ 2) * (1 / (72 * eta ^ 2)) ≤ (1 / 10) / eta ^ 3 := by
    have hpow := pow_le_pow_right₀ he (show 3 ≤ (4 : ℕ) by decide)
    have hi := one_div_le_one_div_of_le (by positivity : 0 < eta ^ 3) hpow
    calc
      _ = (11 / 180) * (1 / eta ^ 4) := by ring
      _ ≤ (11 / 180) * (1 / eta ^ 3) := mul_le_mul_of_nonneg_left hi (by norm_num)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (show (11 / 180 : ℝ) ≤ 1 / 10 by norm_num)
          (by positivity : 0 ≤ 1 / eta ^ 3)
        simpa only [mul_one_div] using h
  have hmain : |p.re * A - p.im * b + (p * E).re - A| ≤ 1 / eta ^ 3 := by
    rw [show p.re * A - p.im * b + (p * E).re - A =
      ((p.re - 1) * A - p.im * b) + (p * E).re by ring]
    have h := abs_sub ((p.re - 1) * A) (p.im * b)
    rw [abs_mul, abs_mul] at h
    exact ((abs_add_le _ _).trans (add_le_add
      (h.trans ((add_le_add hR hI).trans hphase)) hE)).trans_eq (by ring)
  rw [normalized_source_seven_exact h0 h1, ← mul_sub, abs_mul, abs_sourceSignedAmplitude he0.le]
  exact mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg he0.le _)

#print axioms source_extra_correction_allocation
#print axioms normalized_source_seven_original_allocation

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
