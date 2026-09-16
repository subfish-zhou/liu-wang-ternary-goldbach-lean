import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.IntegerSourceBudget
import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceSeven

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization

-- The finite expression, not the pole-crossing integral's totalized endpoint value.
def sourcePolynomialNormalized (eta : ℝ) (m N : ℕ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
    rsLocalPrefactor (1 / 2) eta m *
      (sourceGaussianPhase eta m *
        ∑ k ∈ Finset.range N, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) k *
          (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter eta m)) *
            criticalGammaPhase (sourceTime eta)).re

theorem sourcePolynomialNormalized_seven_noninteger {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    sourcePolynomialNormalized eta m 7 = sourceSevenNormalized eta m := by
  rw [sourcePolynomialNormalized, sourceSevenNormalized,
    sourceLocalPolynomial_integral (1 / 2) h0 h1 7]

theorem normalized_zeta_sourcePolynomial_residual (eta : ℝ) (m N : ℕ) :
    normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) m + sourcePolynomialNormalized eta m N) =
        (sourceZetaPolynomialRemainder (1 / 2) eta m N *
          criticalGammaPhase (sourceTime eta)).re := by
  have hs : sourceFiniteSums (criticalPoint (sourceTime eta)) m *
      criticalGammaPhase (sourceTime eta) =
        (sourceRealMainSum (sourceTime eta) m : ℂ) :=
    source_sums_normalized (sourceTime eta) m
  rw [sourceZetaPolynomialRemainder]
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat]
  rw [source_criticalPoint]
  simp only [sub_mul, sub_re, hs, ← normalizedCriticalZeta_ofReal, ofReal_re,
    sourcePolynomialNormalized]
  ring

theorem normalized_source_remainder_bound (eta : ℝ) (m N : ℕ) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) m + sourcePolynomialNormalized eta m N)| ≤
        ‖sourceZetaPolynomialRemainder (1 / 2) eta m N‖ := by
  rw [normalized_zeta_sourcePolynomial_residual]
  exact (abs_re_le_norm _).trans_eq (by rw [norm_mul, norm_criticalGammaPhase, mul_one])

theorem normalized_source_one_margin {eta : ℝ} (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourcePolynomialNormalized eta ⌊eta⌋₊ 1)| +
        (1 / 125) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) ≤
          (3 / 4) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) :=
  (add_le_add (normalized_source_remainder_bound eta ⌊eta⌋₊ 1) le_rfl).trans
    (complete_source_R0_margin he ht)

theorem normalized_source_seven_margin {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourcePolynomialNormalized eta ⌊eta⌋₊ 7)| +
        (27 / 250) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) ≤
          (57 / 50) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) :=
  (add_le_add (normalized_source_remainder_bound eta ⌊eta⌋₊ 7) le_rfl).trans
    (complete_source_R2_margin he ht)

theorem normalized_source_one_strict {eta : ℝ} (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourcePolynomialNormalized eta ⌊eta⌋₊ 1)| <
        (3 / 4) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have h := normalized_source_one_margin he ht
  have hp := Real.rpow_pos_of_pos (show 0 < eta ^ 2 by linarith) (-(3 / 4 : ℝ))
  linarith

theorem normalized_source_seven_strict {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourcePolynomialNormalized eta ⌊eta⌋₊ 7)| <
        (57 / 50) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have h := normalized_source_seven_margin he ht
  have hp := Real.rpow_pos_of_pos (show 0 < eta ^ 2 by linarith) (-(7 / 4 : ℝ))
  linarith

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
