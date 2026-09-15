import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.UniformPhaseBudget
import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralZetaConsumer

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def sourceLeftNormalized (eta : ℝ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
    (∫ r : ℝ in Ioi 0, rsC2LeftIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ r) *
      criticalGammaPhase (sourceTime eta)).re

def sourceRightNormalized (eta : ℝ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
    (∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ y) *
      criticalGammaPhase (sourceTime eta)).re

def sourcePolynomialExteriorNormalized (eta : ℝ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) * rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ,
      rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y) *
        criticalGammaPhase (sourceTime eta)).re

theorem normalized_zeta_C2_exact {eta : ℝ} {m : ℕ}
    (hm : 0 < m) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    normalizedCriticalZeta (sourceTime eta) =
      sourceRealMainSum (sourceTime eta) m + sourceCentralNormalized eta +
        sourceLeftNormalized eta - sourceRightNormalized eta := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hf : ⌊eta⌋₊ = m := Nat.floor_eq_on_Ico m eta ⟨by linarith, by linarith⟩
  have hz := zeta_eq_C2_local_split hm
    (show 0 < (criticalPoint (sourceTime eta)).im from sourceTime_pos he)
    (show (criticalPoint (sourceTime eta)).re ≤ 1 by norm_num [criticalPoint])
    (show (m : ℝ) < eta by linarith) (show eta < m + 1 by linarith)
  have hn := normalizedCriticalZeta_ofReal (sourceTime eta)
  rw [hz, add_mul, ← sourceChi, source_sums_normalized] at hn
  have hr := congrArg Complex.re hn
  simp only [ofReal_re, add_re, mul_sub, mul_add, sub_mul, add_mul, sub_re] at hr
  simpa only [sourceCentralNormalized, sourceLeftNormalized, sourceRightNormalized,
    rsC2RightIntegrand, hf, mul_sub, mul_add, sub_mul, add_mul, add_re, sub_re,
    add_sub_assoc, add_assoc] using hr

theorem normalized_central_seven_exact {eta : ℝ}
    (he : 0 < eta) (hint : ∀ k : ℤ, eta ≠ k) :
    sourceCentralNormalized eta = sourceSevenNormalized eta ⌊eta⌋₊ +
      sourceJnNormalized eta + sourcePolynomialExteriorNormalized eta := by
  have hf := sourceFraction_floor he.le hint
  have hd := exterior_localHankel_difference (1 / 2) 7 he hint
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hd
  rw [source_criticalPoint, ← sourceLocalPolynomial_integral (1 / 2) hf.1 hf.2 7] at hd
  have hh := congrArg (fun z : ℂ =>
    (rsHankelPrefactor (criticalPoint (sourceTime eta)) * z *
      criticalGammaPhase (sourceTime eta)).re) hd
  dsimp [sourceCentralNormalized, sourceSevenNormalized, sourceJnNormalized,
    sourcePolynomialExteriorNormalized]
  simp only [mul_sub, mul_add, sub_mul, add_mul, sub_re, add_re, mul_assoc] at hh ⊢
  linarith

theorem normalized_zeta_C2_seven_exact {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    normalizedCriticalZeta (sourceTime eta) =
      sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSevenNormalized eta ⌊eta⌋₊ + sourceJnNormalized eta +
          sourcePolynomialExteriorNormalized eta + sourceLeftNormalized eta -
            sourceRightNormalized eta := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  rw [normalized_zeta_C2_exact (Nat.floor_pos.mpr he) hf.1 hf.2,
    normalized_central_seven_exact (by linarith) hint]
  ring

theorem sourceExpandedResidual_eq_original_C2 {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    sourceExpandedResidual eta ⌊eta⌋₊ =
      sourceJnNormalized eta + sourcePolynomialExteriorNormalized eta +
        sourceLeftNormalized eta - sourceRightNormalized eta := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  have hA := normalized_zeta_source_seven_residual (Nat.floor_pos.mpr he) hf.1 hf.2
  have hB := normalized_zeta_C2_seven_exact he hint
  linarith

theorem normalized_zeta_C2_full_phase {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    normalizedCriticalZeta (sourceTime eta) =
      sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ *
          ((sourcePhaseTransport eta).re * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊) -
            (sourcePhaseTransport eta).im * sourceImaginaryCorrection eta (sourcePhiParameter eta ⌊eta⌋₊) +
            (sourcePhaseTransport eta * sourceExtraCorrection eta (sourcePhiParameter eta ⌊eta⌋₊)).re) +
        sourceJnNormalized eta + sourcePolynomialExteriorNormalized eta +
          sourceLeftNormalized eta - sourceRightNormalized eta := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  rw [normalized_zeta_C2_seven_exact he hint, normalized_source_seven_exact hf.1 hf.2]

theorem normalized_zeta_C2_correction_budget {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊) +
        sourceJnNormalized eta + sourceLeftNormalized eta - sourceRightNormalized eta)| ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
          sourceSevenUniformBudget eta (sourcePhiParameter eta ⌊eta⌋₊)) := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  rw [normalized_zeta_C2_exact (Nat.floor_pos.mpr he) hf.1 hf.2]
  have hid (S C A J L R : ℝ) : S + C + L - R - (S + A + J + L - R) = C - J - A := by ring
  rw [hid]
  exact normalized_central_seven_uniform_budget he hint

theorem normalized_zeta_C2_total_budget {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))| ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
          sourceSevenUniformBudget eta (sourcePhiParameter eta ⌊eta⌋₊)) +
        |sourceJnNormalized eta| + |sourceLeftNormalized eta| + |sourceRightNormalized eta| := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  rw [normalized_zeta_C2_exact (Nat.floor_pos.mpr he) hf.1 hf.2]
  have hid (S C A J L R : ℝ) : S + C + L - R - (S + A) = ((C - J - A) + J) + L - R := by ring
  rw [hid _ _ _ (sourceJnNormalized eta)]
  exact (abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (normalized_central_seven_uniform_budget he hint) le_rfl))
      le_rfl)) le_rfl)

theorem normalized_zeta_C2_at_height {t : ℝ}
    (ht : 0 < t) (he : 1 ≤ sourceHeightScale t)
    (hint : ∀ k : ℤ, sourceHeightScale t ≠ k) :
    normalizedCriticalZeta t =
      (2 * ∑ n ∈ Finset.range ⌊sourceHeightScale t⌋₊,
        Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1)) +
      sourceSevenNormalized (sourceHeightScale t) ⌊sourceHeightScale t⌋₊ +
        sourceJnNormalized (sourceHeightScale t) + sourcePolynomialExteriorNormalized (sourceHeightScale t) +
          sourceLeftNormalized (sourceHeightScale t) - sourceRightNormalized (sourceHeightScale t) := by
  simpa only [sourceTime_heightScale ht.le, sourceRealMainSum_cos] using
    normalized_zeta_C2_seven_exact he hint

#print axioms normalized_zeta_C2_full_phase
#print axioms sourceExpandedResidual_eq_original_C2
#print axioms normalized_zeta_C2_correction_budget
#print axioms normalized_zeta_C2_total_budget
#print axioms normalized_zeta_C2_at_height

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
