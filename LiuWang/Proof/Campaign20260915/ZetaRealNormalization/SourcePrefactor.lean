import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceSums
import LiuWang.Proof.Campaign20260915.ZetaMordell.SourceMainTerm

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def sourceTime (eta : ℝ) : ℝ := (rsSaddleScale * eta) ^ 2

def sourceLeadingArgument (eta : ℝ) : ℝ :=
  sourceTime eta * Real.log eta - Real.pi * eta ^ 2 - Real.pi / 8

def sourcePhaseRemainder (eta : ℝ) : ℝ :=
  sourceLeadingArgument eta - criticalGammaArgument (sourceTime eta)

def sourcePhaseTransport (eta : ℝ) : ℂ :=
  exp ((sourcePhaseRemainder eta : ℂ) * I) /
    (1 - I * (Real.exp (-Real.pi * sourceTime eta) : ℂ))

def sourcePhaseBudget (eta : ℝ) : ℝ :=
  |sourceLeadingArgument eta - criticalGammaStirlingArgument (sourceTime eta)| +
    1 / (4 * sourceTime eta) + Real.exp (-Real.pi * sourceTime eta)

def sourceSignedAmplitude (eta : ℝ) (m : ℕ) : ℝ :=
  (-1) ^ (m + 1) * eta ^ (-(1 / 2 : ℝ))

theorem sourceTime_eq (eta : ℝ) : sourceTime eta = 2 * Real.pi * eta ^ 2 := by
  rw [sourceTime, mul_pow, rsSaddleScale_sq]

theorem sourceTime_pos {eta : ℝ} (he : 0 < eta) : 0 < sourceTime eta := by
  rw [sourceTime_eq]
  positivity

theorem source_criticalPoint (eta : ℝ) :
    (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2 =
      criticalPoint (sourceTime eta) := by
  apply Complex.ext <;> simp [criticalPoint, sourceTime, mul_re, mul_im, pow_two]

theorem critical_jump (t : ℝ) :
    exp (Real.pi * I * criticalPoint t) = I * (Real.exp (-Real.pi * t) : ℂ) := by
  have he : Real.pi * I * criticalPoint t =
      ((-Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) / 2 * I := by
    apply Complex.ext <;> simp [criticalPoint, mul_re, mul_im]
    ring
  rw [he, exp_add, exp_pi_div_two_mul_I, ofReal_exp, mul_comm]

theorem source_denominator_norm (t : ℝ) :
    1 ≤ ‖(1 : ℂ) - I * (Real.exp (-Real.pi * t) : ℂ)‖ := by
  simpa only [sub_re, one_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, mul_zero, sub_zero, abs_one] using
    abs_re_le_norm ((1 : ℂ) - I * (Real.exp (-Real.pi * t) : ℂ))

theorem source_denominator_ne_zero (t : ℝ) :
    (1 : ℂ) - I * (Real.exp (-Real.pi * t) : ℂ) ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (source_denominator_norm t))

theorem sourcePhaseTransport_norm (eta : ℝ) : ‖sourcePhaseTransport eta‖ ≤ 1 := by
  rw [sourcePhaseTransport, norm_div, norm_exp_ofReal_mul_I]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (source_denominator_norm _))).mpr
    (source_denominator_norm _)

theorem sourcePhaseTransport_distance (eta : ℝ) :
    ‖sourcePhaseTransport eta - 1‖ ≤
      |sourcePhaseRemainder eta| + Real.exp (-Real.pi * sourceTime eta) := by
  let u : ℂ := exp ((sourcePhaseRemainder eta : ℂ) * I)
  let q : ℝ := Real.exp (-Real.pi * sourceTime eta)
  have hd : (1 : ℂ) - I * (q : ℂ) ≠ 0 := source_denominator_ne_zero _
  have he : sourcePhaseTransport eta - 1 =
      ((u - 1) + I * (q : ℂ)) / (1 - I * (q : ℂ)) := by
    change u / (1 - I * (q : ℂ)) - 1 = _
    field_simp [hd]
    ring
  have hu : ‖u - 1‖ ≤ |sourcePhaseRemainder eta| := by
    simpa [u] using unitPhase_distance_le (sourcePhaseRemainder eta) 0
  rw [he, norm_div]
  calc
    _ ≤ ‖(u - 1) + I * (q : ℂ)‖ :=
      div_le_self (norm_nonneg _) (source_denominator_norm _)
    _ ≤ ‖u - 1‖ + ‖I * (q : ℂ)‖ := norm_add_le _ _
    _ ≤ |sourcePhaseRemainder eta| + q := by
      simpa only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        show |q| = q from abs_of_pos (Real.exp_pos _), add_comm] using
        add_le_add_right hu ‖I * (q : ℂ)‖

theorem sourcePhaseTransport_stirling_budget {eta : ℝ} (he : 0 < eta) :
    ‖sourcePhaseTransport eta - 1‖ ≤ sourcePhaseBudget eta := by
  have ht := criticalGammaStirlingArgument_error (sourceTime_pos he)
  have ha := abs_sub_le (sourceLeadingArgument eta)
    (criticalGammaStirlingArgument (sourceTime eta)) (criticalGammaArgument (sourceTime eta))
  rw [abs_sub_comm (criticalGammaStirlingArgument _)] at ha
  exact (sourcePhaseTransport_distance eta).trans (by
    dsimp [sourcePhaseRemainder, sourcePhaseBudget]
    linarith)

theorem source_gaussian_critical {eta : ℝ} (he : 0 < eta) (m : ℕ) :
    rsLocalPrefactor (1 / 2) eta m * sourceGaussianPhase eta m =
      ((-1 : ℂ) ^ m * ((eta ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        exp ((sourceLeadingArgument eta : ℂ) * I) := by
  rw [sourceGaussian_prefactor]
  have hp :
      (eta : ℂ) ^ (((1 / 2 : ℝ) : ℂ) +
        I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2 - 1) =
      ((eta ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        exp (((sourceTime eta * Real.log eta : ℝ) : ℂ) * I) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr he.ne'),
      Real.rpow_def_of_pos he, ofReal_exp, ← exp_add, ← ofReal_log he.le]
    congr 1
    apply Complex.ext <;> simp [sourceTime, mul_re, mul_im, pow_two] <;> ring
  rw [hp]
  have hexp : exp (-Real.pi * I / 8) *
      exp (((sourceTime eta * Real.log eta : ℝ) : ℂ) * I) *
      exp (-Real.pi * I * (eta : ℂ) ^ 2) =
        exp ((sourceLeadingArgument eta : ℂ) * I) := by
    rw [← exp_add, ← exp_add]
    congr 1
    unfold sourceLeadingArgument
    push_cast
    ring
  linear_combination ((-1 : ℂ) ^ m * ((eta ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * hexp

theorem normalized_source_prefactor {eta : ℝ} (he : 0 < eta) (m : ℕ) :
    rsHankelPrefactor (criticalPoint (sourceTime eta)) *
      rsLocalPrefactor (1 / 2) eta m * sourceGaussianPhase eta m *
        criticalGammaPhase (sourceTime eta) =
      (sourceSignedAmplitude eta m : ℂ) * sourcePhaseTransport eta := by
  have h := hankel_phase_exact (sourceTime_pos he)
  rw [critical_jump, criticalGammaPhase_eq_exp_argument, ← exp_conj] at h
  have hc : conj ((criticalGammaArgument (sourceTime eta) : ℂ) * I) =
      -((criticalGammaArgument (sourceTime eta) : ℂ) * I) := by simp
  rw [hc] at h
  have hl := source_gaussian_critical he m
  have hexp : exp (-((criticalGammaArgument (sourceTime eta) : ℂ) * I)) *
      exp ((sourceLeadingArgument eta : ℂ) * I) =
        exp ((sourcePhaseRemainder eta : ℂ) * I) := by
    rw [← exp_add]
    congr 1
    unfold sourcePhaseRemainder
    push_cast
    ring
  calc
    _ = (rsHankelPrefactor (criticalPoint (sourceTime eta)) *
        criticalGammaPhase (sourceTime eta)) *
        (rsLocalPrefactor (1 / 2) eta m * sourceGaussianPhase eta m) := by ring
    _ = _ := by
      rw [criticalGammaPhase_eq_exp_argument, h, hl]
      rw [show I * (Real.exp (-Real.pi * sourceTime eta) : ℂ) - 1 =
        -(1 - I * (Real.exp (-Real.pi * sourceTime eta) : ℂ)) by ring, div_neg]
      calc
        _ = -((-1 : ℂ) ^ m * ((eta ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
            (exp (-((criticalGammaArgument (sourceTime eta) : ℂ) * I)) *
              exp ((sourceLeadingArgument eta : ℂ) * I)) /
            (1 - I * (Real.exp (-Real.pi * sourceTime eta) : ℂ)) := by ring
        _ = _ := by
          rw [hexp]
          simp only [sourceSignedAmplitude, sourcePhaseTransport, ofReal_mul,
            ofReal_pow, ofReal_neg, ofReal_one, pow_succ]
          ring

theorem abs_sourceSignedAmplitude {eta : ℝ} (he : 0 ≤ eta) (m : ℕ) :
    |sourceSignedAmplitude eta m| = eta ^ (-(1 / 2 : ℝ)) := by
  simp [sourceSignedAmplitude, abs_mul, abs_pow,
    abs_of_nonneg (Real.rpow_nonneg he _)]

#print axioms normalized_source_prefactor
#print axioms sourcePhaseTransport_stirling_budget

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
