import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.MomentBudget
import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorLocalHankel

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def sourceCentralNormalized (eta : ℝ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel (criticalPoint (sourceTime eta)) ⌊eta⌋₊ (rsDescentPoint eta y)) *
        criticalGammaPhase (sourceTime eta)).re

def sourceJnNormalized (eta : ℝ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
    rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y) *
        criticalGammaPhase (sourceTime eta)).re

def sourceExpandedResidual (eta : ℝ) (m : ℕ) : ℝ :=
  (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
    (rsHankelTiltedC1 (criticalPoint (sourceTime eta)) m (Real.log eta) -
      rsLocalPrefactor (1 / 2) eta m *
        (-(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y))) *
      criticalGammaPhase (sourceTime eta)).re

theorem hankel_critical_norm {t : ℝ} (ht : 0 < t) :
    ‖rsHankelPrefactor (criticalPoint t)‖ ≤ 1 := by
  have h := congrArg norm (hankel_phase_exact ht)
  rw [norm_mul, norm_criticalGammaPhase, mul_one, norm_div, norm_conj,
    norm_criticalGammaPhase, critical_jump, norm_sub_rev] at h
  rw [h]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (source_denominator_norm t))).mpr
    (source_denominator_norm t)

theorem hankel_normalized_re_bound {t : ℝ} (ht : 0 < t) (D : ℂ) :
    |(rsHankelPrefactor (criticalPoint t) * D * criticalGammaPhase t).re| ≤ ‖D‖ := by
  calc
    _ ≤ ‖rsHankelPrefactor (criticalPoint t) * D * criticalGammaPhase t‖ := abs_re_le_norm _
    _ = ‖rsHankelPrefactor (criticalPoint t)‖ * ‖D‖ := by
      rw [norm_mul, norm_mul, norm_criticalGammaPhase, mul_one]
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hankel_critical_norm ht)
        (norm_nonneg D)

theorem normalized_central_seven_exterior {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta - sourceSevenNormalized eta ⌊eta⌋₊ - sourceJnNormalized eta| ≤
      eta ^ (-(1 / 2 : ℝ)) * (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8)) := by
  have he0 : 0 < eta := by linarith
  have hf := sourceFraction_floor he0.le hint
  have hb := exterior_localHankel_seven he hint
  rw [source_criticalPoint, ← sourceLocalPolynomial_integral (1 / 2) hf.1 hf.2 7] at hb
  let D : ℂ :=
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel (criticalPoint (sourceTime eta)) ⌊eta⌋₊ (rsDescentPoint eta y)) -
    rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
      (-(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y) +
        ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y)
  have hid :
      sourceCentralNormalized eta - sourceSevenNormalized eta ⌊eta⌋₊ - sourceJnNormalized eta =
        (rsHankelPrefactor (criticalPoint (sourceTime eta)) * D *
          criticalGammaPhase (sourceTime eta)).re := by
    dsimp [sourceCentralNormalized, sourceSevenNormalized, sourceJnNormalized, D]
    simp only [mul_sub, mul_add, sub_mul, add_mul, sub_re, add_re, mul_assoc]
    ring
  rw [hid]
  exact (hankel_normalized_re_bound (sourceTime_pos he0) D).trans hb

theorem normalized_central_seven_budget {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta - sourceJnNormalized eta -
      sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊)| ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
          sourcePhaseBudget eta *
            (|sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊)| +
              |sourceImaginaryCorrection eta (sourcePhiParameter eta ⌊eta⌋₊)|) +
          sourceExtraDerivativeBudget eta (sourcePhiParameter eta ⌊eta⌋₊)) := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  have hb := normalized_source_seven_derivative_budget hf.1 hf.2
  have hc := normalized_central_seven_exterior he hint
  have hh := abs_add_le
    (sourceCentralNormalized eta - sourceSevenNormalized eta ⌊eta⌋₊ - sourceJnNormalized eta)
    (sourceSevenNormalized eta ⌊eta⌋₊ -
      sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))
  have hid :
      (sourceCentralNormalized eta - sourceSevenNormalized eta ⌊eta⌋₊ - sourceJnNormalized eta) +
        (sourceSevenNormalized eta ⌊eta⌋₊ -
          sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊)) =
      sourceCentralNormalized eta - sourceJnNormalized eta -
        sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊) := by ring
  rw [hid] at hh
  exact (hh.trans (add_le_add hc hb)).trans_eq (by ring)

theorem normalized_zeta_source_seven_residual {eta : ℝ} {m : ℕ}
    (hm : 0 < m) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    normalizedCriticalZeta (sourceTime eta) =
      sourceRealMainSum (sourceTime eta) m +
        sourceSevenNormalized eta m + sourceExpandedResidual eta m := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [normalizedCriticalZeta_expanded hm (sourceTime_pos he)
    (show (m : ℝ) < eta by linarith) (show eta < m + 1 by linarith)]
  simp only [sourceSevenNormalized, sourceExpandedResidual, mul_sub, sub_mul,
    sub_re, mul_assoc]
  ring

theorem normalized_zeta_source_seven_budget {eta : ℝ} {m : ℕ}
    (hm : 0 < m) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) m +
        sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m))| ≤
      |sourceExpandedResidual eta m| +
        eta ^ (-(1 / 2 : ℝ)) *
          (sourcePhaseBudget eta *
            (|sourceRealCorrection eta (sourcePhiParameter eta m)| +
              |sourceImaginaryCorrection eta (sourcePhiParameter eta m)|) +
            sourceExtraDerivativeBudget eta (sourcePhiParameter eta m)) := by
  rw [normalized_zeta_source_seven_residual hm h0 h1]
  have hid (S P E A : ℝ) : S + P + E - (S + A) = E + (P - A) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add le_rfl
    (normalized_source_seven_derivative_budget h0 h1))

#print axioms normalized_central_seven_budget
#print axioms normalized_zeta_source_seven_residual
#print axioms normalized_zeta_source_seven_budget

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
