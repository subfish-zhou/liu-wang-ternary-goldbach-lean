import LiuWang.Proof.Campaign20260915.ZetaMordell.ParameterDerivatives
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped Real ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

-- Siegel's 0 ↖ 1: southeast to northwest, with the negative quadratic phase.
def siegelLine (t : ℝ) : ℂ := 1 / 2 + (-1 + I) * t

def siegelKernel (u : ℂ) (t : ℝ) : ℂ :=
  exp (-Real.pi * I * siegelLine t ^ 2 + 2 * Real.pi * I * u * siegelLine t) /
    (exp (Real.pi * I * siegelLine t) - exp (-Real.pi * I * siegelLine t)) * (-1 + I)

def siegelIntegral (u : ℂ) : ℂ := ∫ t : ℝ, siegelKernel u t

def siegelWeightedKernel (n : ℕ) (u : ℂ) (t : ℝ) : ℂ :=
  (2 * Real.pi * I * siegelLine t) ^ n * siegelKernel u t

def siegelMoment (n : ℕ) (u : ℂ) : ℂ := ∫ t : ℝ, siegelWeightedKernel n u t

theorem siegelLine_hasDerivAt (t : ℝ) :
    HasDerivAt siegelLine (-1 + I) t := by
  change HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + (-1 + I) * t) (-1 + I) t
  simpa using
    ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-1 + I)).const_add (1 / 2 : ℂ)

theorem siegelLine_conj (t : ℝ) : conj (mordellLine (-t)) = siegelLine t := by
  simp [mordellLine, siegelLine, conj_ofNat]
  ring

private theorem exp_denominator_normalization (A B d : ℂ) :
    exp (A - B) / (exp (-2 * B) - 1) * (-d) =
      exp A / (exp B - exp (-B)) * d := by
  have he : exp (-2 * B) - 1 = -exp (-B) * (exp B - exp (-B)) := by
    have h1 : exp (-B) * exp B = 1 := by rw [← exp_add]; simp
    have h2 : exp (-B) * exp (-B) = exp (-2 * B) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      exp (-2 * B) - 1 = exp (-B) * exp (-B) - exp (-B) * exp B := by rw [h1, h2]
      _ = _ := by ring
  rw [he, sub_eq_add_neg, exp_add, div_eq_mul_inv, mul_inv_rev, inv_neg]
  have hn := exp_ne_zero (-B)
  rw [show exp A * exp (-B) * ((exp B - exp (-B))⁻¹ * -(exp (-B))⁻¹) * -d =
    exp A * (exp B - exp (-B))⁻¹ * d * (exp (-B) * (exp (-B))⁻¹) by ring]
  rw [mul_inv_cancel₀ hn, mul_one, div_eq_mul_inv]

theorem siegelKernel_conj (u : ℂ) (t : ℝ) :
    siegelKernel u t = conj (mordellKernel (1 / 2 - conj u) (-t)) := by
  simp only [mordellKernel, mordellGaussian, mordellDenominator, map_mul, map_div₀,
    map_sub, map_add, map_pow, conj_ofNat, map_one, conj_ofReal, conj_I,
    ← Complex.exp_conj, conj_conj, siegelLine_conj]
  have hA :
      (Real.pi : ℂ) * -I * siegelLine t ^ 2 +
        2 * Real.pi * -I * (1 / 2 - u) * siegelLine t =
      (-Real.pi * I * siegelLine t ^ 2 + 2 * Real.pi * I * u * siegelLine t) -
        Real.pi * I * siegelLine t := by ring
  have hB : 2 * (Real.pi : ℂ) * -I * siegelLine t =
      -2 * (Real.pi * I * siegelLine t) := by ring
  rw [hA, hB, show (1 : ℂ) + -I = -(-1 + I) by ring, exp_denominator_normalization]
  simp only [siegelKernel, neg_mul]

theorem siegelWeightedKernel_conj (n : ℕ) (u : ℂ) (t : ℝ) :
    siegelWeightedKernel n u t =
      (-1 : ℂ) ^ n * conj (mordellWeightedKernel n (1 / 2 - conj u) (-t)) := by
  rw [siegelWeightedKernel, siegelKernel_conj]
  simp only [mordellWeightedKernel, map_mul, map_pow, map_ofNat, conj_ofReal,
    conj_I, siegelLine_conj]
  rw [← mul_assoc, ← mul_pow]
  congr 1
  ring

theorem siegelWeightedKernel_integrable (n : ℕ) (u : ℂ) :
    Integrable (siegelWeightedKernel n u) := by
  have h := (mordellWeightedKernel_integrable n (1 / 2 - conj u)).comp_neg
  have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h
  change Integrable (fun t : ℝ => siegelWeightedKernel n u t)
  simp_rw [siegelWeightedKernel_conj]
  exact hc.const_mul ((-1 : ℂ) ^ n)

theorem siegelKernel_integrable (u : ℂ) : Integrable (siegelKernel u) := by
  have h := siegelWeightedKernel_integrable 0 u
  change Integrable (fun t : ℝ => siegelWeightedKernel 0 u t) at h
  change Integrable (fun t : ℝ => siegelKernel u t)
  simpa only [siegelWeightedKernel, pow_zero, one_mul] using h

theorem siegelMoment_conj (n : ℕ) (u : ℂ) :
    siegelMoment n u = (-1 : ℂ) ^ n * conj (mordellMoment n (1 / 2 - conj u)) := by
  unfold siegelMoment mordellMoment
  simp_rw [siegelWeightedKernel_conj]
  rw [integral_const_mul, integral_conj, integral_neg_eq_self]

theorem siegelIntegral_conj (u : ℂ) :
    siegelIntegral u = conj (mordellIntegral (1 / 2 - conj u)) := by
  unfold siegelIntegral mordellIntegral
  simp_rw [siegelKernel_conj]
  rw [integral_conj, integral_neg_eq_self]

theorem siegelMoment_hasDerivAt (n : ℕ) (u : ℂ) :
    HasDerivAt (siegelMoment n) (siegelMoment (n + 1) u) u := by
  have h := (mordellMoment_hasDerivAt n (1 / 2 - conj u)).comp (conj u)
    ((hasDerivAt_id (conj u)).const_sub (1 / 2 : ℂ))
  have hc := h.conj_conj.const_mul ((-1 : ℂ) ^ n)
  simp only [conj_conj, Function.comp_def, mul_neg, mul_one, map_neg] at hc
  have he : (fun z : ℂ => (-1 : ℂ) ^ n *
      conj (mordellMoment n (1 / 2 - conj z))) = siegelMoment n :=
    funext (fun z => (siegelMoment_conj n z).symm)
  rw [he] at hc
  convert! hc using 1
  rw [siegelMoment_conj, pow_succ]
  ring

theorem siegelMoment_zero : siegelMoment 0 = siegelIntegral := by
  ext u
  simp [siegelMoment, siegelWeightedKernel, siegelIntegral]

theorem siegelIntegral_iteratedDeriv (n : ℕ) :
    iteratedDeriv n siegelIntegral = siegelMoment n := by
  induction n with
  | zero => simpa using siegelMoment_zero.symm
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun u => (siegelMoment_hasDerivAt n u).deriv)

end LiuWang.Proof.Campaign20260915.ZetaMordell
