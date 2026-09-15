import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceConsumer

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def sourceGammaPhaseBudget (eta : ℝ) : ℝ :=
  |sourceLeadingArgument eta - criticalGammaStirlingArgument (sourceTime eta)| +
    1 / (4 * sourceTime eta)

def sourceRealPhaseBudget (eta : ℝ) : ℝ :=
  sourceGammaPhaseBudget eta ^ 2 / 2 + Real.exp (-Real.pi * sourceTime eta)

def sourceSevenRealBudget (eta z : ℝ) : ℝ :=
  sourceRealPhaseBudget eta * |sourceRealCorrection eta z| +
    sourcePhaseBudget eta * |sourceImaginaryCorrection eta z| +
    sourceExtraDerivativeBudget eta z

theorem sourcePhaseRemainder_bound {eta : ℝ} (he : 0 < eta) :
    |sourcePhaseRemainder eta| ≤ sourceGammaPhaseBudget eta := by
  have ht := criticalGammaStirlingArgument_error (sourceTime_pos he)
  have ha := abs_sub_le (sourceLeadingArgument eta)
    (criticalGammaStirlingArgument (sourceTime eta)) (criticalGammaArgument (sourceTime eta))
  rw [abs_sub_comm (criticalGammaStirlingArgument _)] at ha
  dsimp [sourcePhaseRemainder, sourceGammaPhaseBudget]
  linarith

theorem sourcePhaseTransport_unit_distance (eta : ℝ) :
    ‖sourcePhaseTransport eta - exp ((sourcePhaseRemainder eta : ℂ) * I)‖ ≤
      Real.exp (-Real.pi * sourceTime eta) := by
  let u : ℂ := exp ((sourcePhaseRemainder eta : ℂ) * I)
  let q : ℝ := Real.exp (-Real.pi * sourceTime eta)
  have hd : (1 : ℂ) - I * (q : ℂ) ≠ 0 := source_denominator_ne_zero _
  have hid : sourcePhaseTransport eta - u = u * (I * (q : ℂ)) / (1 - I * (q : ℂ)) := by
    change u / (1 - I * (q : ℂ)) - u = _
    field_simp [hd]
    ring
  change ‖sourcePhaseTransport eta - u‖ ≤ q
  rw [hid, norm_div, norm_mul, norm_mul,
    show ‖u‖ = 1 from norm_exp_ofReal_mul_I _, norm_I, one_mul, one_mul,
    norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact div_le_self (Real.exp_pos _).le (source_denominator_norm _)

theorem sourcePhaseTransport_re_bound {eta : ℝ} (he : 0 < eta) :
    |(sourcePhaseTransport eta).re - 1| ≤ sourceRealPhaseBudget eta := by
  let u : ℂ := exp ((sourcePhaseRemainder eta : ℂ) * I)
  have hu : ‖u‖ = 1 := norm_exp_ofReal_mul_I _
  have hd0 : ‖u - 1‖ ≤ |sourcePhaseRemainder eta| := by
    simpa only [u, ofReal_zero, zero_mul, exp_zero, sub_zero] using
      unitPhase_distance_le (sourcePhaseRemainder eta) 0
  have hd := hd0.trans (sourcePhaseRemainder_bound he)
  have hr : u.re ≤ 1 := (re_le_norm u).trans_eq hu
  have hs := norm_sub_one_sq_eq_of_norm_eq_one hu
  have hsq := pow_le_pow_left₀ (norm_nonneg (u - 1)) hd 2
  have hu' : |u.re - 1| ≤ sourceGammaPhaseBudget eta ^ 2 / 2 := by
    rw [abs_of_nonpos (by linarith : u.re - 1 ≤ 0)]
    nlinarith
  have hp0 : |(sourcePhaseTransport eta).re - u.re| ≤ ‖sourcePhaseTransport eta - u‖ := by
    simpa only [sub_re] using abs_re_le_norm (sourcePhaseTransport eta - u)
  have hp := hp0.trans (sourcePhaseTransport_unit_distance eta)
  exact ((abs_sub_le (sourcePhaseTransport eta).re u.re 1).trans
    (add_le_add hp hu')).trans_eq (by unfold sourceRealPhaseBudget; ring)

theorem sourcePhaseTransport_im_bound {eta : ℝ} (he : 0 < eta) :
    |(sourcePhaseTransport eta).im| ≤ sourcePhaseBudget eta := by
  have h : |(sourcePhaseTransport eta).im| ≤ ‖sourcePhaseTransport eta - 1‖ := by
    simpa only [sub_im, one_im, sub_zero] using abs_im_le_norm (sourcePhaseTransport eta - 1)
  exact h.trans (sourcePhaseTransport_stirling_budget he)

theorem normalized_source_seven_real_budget {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |sourceSevenNormalized eta m -
      sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m)| ≤
        eta ^ (-(1 / 2 : ℝ)) * sourceSevenRealBudget eta (sourcePhiParameter eta m) := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  let A := sourceRealCorrection eta (sourcePhiParameter eta m)
  let b := sourceImaginaryCorrection eta (sourcePhiParameter eta m)
  let E := sourceExtraCorrection eta (sourcePhiParameter eta m)
  let p := sourcePhaseTransport eta
  have hE : |(p * E).re| ≤ sourceExtraDerivativeBudget eta (sourcePhiParameter eta m) := by
    calc
      _ ≤ ‖p * E‖ := abs_re_le_norm _
      _ ≤ ‖E‖ := by
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (sourcePhaseTransport_norm eta) (norm_nonneg E)
      _ ≤ _ := (sourceExtraCorrection_bound he _).trans
        (sourceExtraBudget_le_derivative he (sourcePhiParameter_domain h0.le h1.le))
  have hmain :
      |p.re * A - p.im * b + (p * E).re - A| ≤
        sourceRealPhaseBudget eta * |A| + sourcePhaseBudget eta * |b| +
          sourceExtraDerivativeBudget eta (sourcePhiParameter eta m) := by
    rw [show p.re * A - p.im * b + (p * E).re - A =
      ((p.re - 1) * A - p.im * b) + (p * E).re by ring]
    calc
      _ ≤ |(p.re - 1) * A - p.im * b| + |(p * E).re| := abs_add_le _ _
      _ ≤ (|p.re - 1| * |A| + |p.im| * |b|) + |(p * E).re| := by
        have hh := abs_sub ((p.re - 1) * A) (p.im * b)
        rw [abs_mul, abs_mul] at hh
        exact add_le_add hh le_rfl
      _ ≤ _ := add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (sourcePhaseTransport_re_bound he) (abs_nonneg A))
        (mul_le_mul_of_nonneg_right (sourcePhaseTransport_im_bound he) (abs_nonneg b))) hE
  rw [normalized_source_seven_exact h0 h1, ← mul_sub, abs_mul, abs_sourceSignedAmplitude he.le]
  exact mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg he.le _)

theorem normalized_central_seven_real_budget {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta - sourceJnNormalized eta -
      sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊)| ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
          sourceSevenRealBudget eta (sourcePhiParameter eta ⌊eta⌋₊)) := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  have hb := normalized_source_seven_real_budget hf.1 hf.2
  have hc := normalized_central_seven_exterior he hint
  have hid (C P J A : ℝ) : C - J - A = (C - P - J) + (P - A) := by ring
  rw [hid _ (sourceSevenNormalized eta ⌊eta⌋₊)]
  exact ((abs_add_le _ _).trans (add_le_add hc hb)).trans_eq (by ring)

theorem normalized_zeta_source_seven_real_budget {eta : ℝ} {m : ℕ}
    (hm : 0 < m) (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) m +
        sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m))| ≤
      |sourceExpandedResidual eta m| +
        eta ^ (-(1 / 2 : ℝ)) * sourceSevenRealBudget eta (sourcePhiParameter eta m) := by
  rw [normalized_zeta_source_seven_residual hm h0 h1]
  have hid (S P E A : ℝ) : S + P + E - (S + A) = E + (P - A) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (normalized_source_seven_real_budget h0 h1))

#print axioms sourcePhaseTransport_re_bound
#print axioms normalized_central_seven_real_budget
#print axioms normalized_zeta_source_seven_real_budget

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
