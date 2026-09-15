import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourcePrefactor

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def sourceRealCorrection (eta z : ℝ) : ℝ :=
  rsPhi z - rsPhiOne z / eta + rsPhiTwo z / eta ^ 2

def sourceImaginaryCorrection (eta z : ℝ) : ℝ :=
  rsPhi z / (96 * Real.pi * eta ^ 2)

def sourceExtraCorrection (eta z : ℝ) : ℂ :=
  -(5 / (16 * (eta : ℂ) ^ 3)) * correctionMoment 3 z +
    35 / (128 * (eta : ℂ) ^ 4) * correctionMoment 4 z +
    (9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) - 63 / (256 * (eta : ℂ) ^ 5)) *
      correctionMoment 5 z +
    (-(223 * Real.pi * I) / (240 * (eta : ℂ) ^ 4) + 231 / (1024 * (eta : ℂ) ^ 6)) *
      correctionMoment 6 z

def sourceExtraBudget (eta z : ℝ) : ℝ :=
  5 / (16 * eta ^ 3) * ‖correctionMoment 3 z‖ +
    35 / (128 * eta ^ 4) * ‖correctionMoment 4 z‖ +
    (9 * Real.pi / (10 * eta ^ 3) + 63 / (256 * eta ^ 5)) * ‖correctionMoment 5 z‖ +
    (223 * Real.pi / (240 * eta ^ 4) + 231 / (1024 * eta ^ 6)) * ‖correctionMoment 6 z‖

def sourceSevenNormalized (eta : ℝ) (m : ℕ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
    rsLocalPrefactor (1 / 2) eta m *
      (-(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y)) *
        criticalGammaPhase (sourceTime eta)).re

theorem source_seven_decomposition {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    -(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y) =
      sourceGaussianPhase eta m *
        ((sourceRealCorrection eta (sourcePhiParameter eta m) : ℂ) +
          I * (sourceImaginaryCorrection eta (sourcePhiParameter eta m) : ℂ) +
          sourceExtraCorrection eta (sourcePhiParameter eta m)) := by
  rw [sourceLocalPolynomial_seven_phi h0 h1]
  unfold sourceRealCorrection sourceImaginaryCorrection sourceExtraCorrection
  push_cast
  ring

theorem sourceExtraCorrection_bound {eta : ℝ} (he : 0 < eta) (z : ℝ) :
    ‖sourceExtraCorrection eta z‖ ≤ sourceExtraBudget eta z := by
  have h5 :
      ‖9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) - 63 / (256 * (eta : ℂ) ^ 5)‖ ≤
        9 * Real.pi / (10 * eta ^ 3) + 63 / (256 * eta ^ 5) := by
    calc
      _ ≤ ‖9 * Real.pi * I / (10 * (eta : ℂ) ^ 3)‖ +
          ‖(63 : ℂ) / (256 * (eta : ℂ) ^ 5)‖ := norm_sub_le _ _
      _ = _ := by
        simp only [norm_div, norm_mul, norm_pow, norm_I, norm_ofNat, norm_real,
          Real.norm_eq_abs, abs_of_pos he, abs_of_pos Real.pi_pos, mul_one]
  have h6 :
      ‖-(223 * Real.pi * I) / (240 * (eta : ℂ) ^ 4) + 231 / (1024 * (eta : ℂ) ^ 6)‖ ≤
        223 * Real.pi / (240 * eta ^ 4) + 231 / (1024 * eta ^ 6) := by
    calc
      _ ≤ ‖-(223 * Real.pi * I) / (240 * (eta : ℂ) ^ 4)‖ +
          ‖(231 : ℂ) / (1024 * (eta : ℂ) ^ 6)‖ := norm_add_le _ _
      _ = _ := by
        simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_I, norm_ofNat, norm_real,
          Real.norm_eq_abs, abs_of_pos he, abs_of_pos Real.pi_pos, mul_one]
  unfold sourceExtraCorrection sourceExtraBudget
  calc
    _ ≤ (‖-(5 / (16 * (eta : ℂ) ^ 3)) * correctionMoment 3 z‖ +
        ‖35 / (128 * (eta : ℂ) ^ 4) * correctionMoment 4 z‖) +
        ‖(9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) - 63 / (256 * (eta : ℂ) ^ 5)) *
          correctionMoment 5 z‖ +
        ‖(-(223 * Real.pi * I) / (240 * (eta : ℂ) ^ 4) +
          231 / (1024 * (eta : ℂ) ^ 6)) * correctionMoment 6 z‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul, norm_neg, norm_div, norm_pow, norm_ofNat,
        norm_real, Real.norm_eq_abs, abs_of_pos he]
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right h5 (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right h6 (norm_nonneg _))

theorem normalized_source_seven_exact {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    sourceSevenNormalized eta m = sourceSignedAmplitude eta m *
      ((sourcePhaseTransport eta).re * sourceRealCorrection eta (sourcePhiParameter eta m) -
        (sourcePhaseTransport eta).im * sourceImaginaryCorrection eta (sourcePhiParameter eta m) +
        (sourcePhaseTransport eta * sourceExtraCorrection eta (sourcePhiParameter eta m)).re) := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  unfold sourceSevenNormalized
  rw [source_seven_decomposition h0 h1]
  have hp := normalized_source_prefactor he m
  have hh (P : ℂ) :
      rsHankelPrefactor (criticalPoint (sourceTime eta)) * rsLocalPrefactor (1 / 2) eta m *
          (sourceGaussianPhase eta m * P) * criticalGammaPhase (sourceTime eta) =
        (sourceSignedAmplitude eta m : ℂ) * (sourcePhaseTransport eta * P) := by
    linear_combination P * hp
  rw [hh]
  simp only [mul_add, add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

theorem phase_real_correction_bound {p E : ℂ} {d : ℝ}
    (hp : ‖p‖ ≤ 1) (hd : ‖p - 1‖ ≤ d) (A b : ℝ) :
    |(p * ((A : ℂ) + I * (b : ℂ) + E)).re - A| ≤
      d * (|A| + |b|) + ‖E‖ := by
  have hr :
      (p * ((A : ℂ) + I * (b : ℂ) + E)).re - A =
        ((p - 1) * ((A : ℂ) + I * (b : ℂ)) + p * E).re := by
    simp only [mul_add, sub_mul, add_re, sub_re, one_mul, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hab : ‖(A : ℂ) + I * (b : ℂ)‖ ≤ |A| + |b| := by
    simpa only [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs] using
      norm_add_le (A : ℂ) (I * (b : ℂ))
  rw [hr]
  calc
    _ ≤ ‖(p - 1) * ((A : ℂ) + I * (b : ℂ)) + p * E‖ := abs_re_le_norm _
    _ ≤ ‖p - 1‖ * ‖(A : ℂ) + I * (b : ℂ)‖ + ‖p‖ * ‖E‖ := by
      simpa only [norm_mul] using
        norm_add_le ((p - 1) * ((A : ℂ) + I * (b : ℂ))) (p * E)
    _ ≤ _ := by
      simpa only [one_mul] using add_le_add
        (mul_le_mul hd hab (norm_nonneg _) ((norm_nonneg _).trans hd))
        (mul_le_mul_of_nonneg_right hp (norm_nonneg _))

theorem normalized_source_seven_budget {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |sourceSevenNormalized eta m -
      sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m)| ≤
        eta ^ (-(1 / 2 : ℝ)) *
          (sourcePhaseBudget eta *
            (|sourceRealCorrection eta (sourcePhiParameter eta m)| +
              |sourceImaginaryCorrection eta (sourcePhiParameter eta m)|) +
            sourceExtraBudget eta (sourcePhiParameter eta m)) := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hb := phase_real_correction_bound (E := sourceExtraCorrection eta (sourcePhiParameter eta m))
    (sourcePhaseTransport_norm eta) (sourcePhaseTransport_stirling_budget he)
    (sourceRealCorrection eta (sourcePhiParameter eta m))
    (sourceImaginaryCorrection eta (sourcePhiParameter eta m))
  have hr (A b : ℝ) (E : ℂ) :
      (sourcePhaseTransport eta * ((A : ℂ) + I * (b : ℂ) + E)).re =
        (sourcePhaseTransport eta).re * A - (sourcePhaseTransport eta).im * b +
          (sourcePhaseTransport eta * E).re := by
    simp only [mul_add, add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  rw [hr] at hb
  rw [normalized_source_seven_exact h0 h1, ← mul_sub, abs_mul, abs_sourceSignedAmplitude he.le]
  exact mul_le_mul_of_nonneg_left
    (hb.trans (add_le_add le_rfl (sourceExtraCorrection_bound he _)))
    (Real.rpow_nonneg he.le _)

#print axioms normalized_source_seven_exact
#print axioms normalized_source_seven_budget

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
