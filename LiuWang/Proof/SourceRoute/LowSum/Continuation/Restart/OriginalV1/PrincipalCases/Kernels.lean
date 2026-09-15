import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CaseIV
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SelectedZeroSum

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

def gammaHalfDifference (sigma t : ℝ) : ℝ :=
  ((Complex.digamma (((sigma : ℂ) + I * t) / 2 + 1)).re -
    stechkinK * (Complex.digamma (((stechkinSigma sigma : ℂ) + I * t) / 2 + 1)).re) / 2

theorem shiftedGamma_eq (sigma t : ℝ) :
    shiftedGammaDifference sigma t =
      -stechkinConductorCoeff * Real.log Real.pi + gammaHalfDifference sigma t := rfl

theorem realKernel_eq_inverse_re (a u : ℝ) :
    realKernel a u = (1 / ((a : ℂ) + I * u)).re := by
  simp [realKernel, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, pow_two]

theorem lwd_G_lemma_two {sigma beta gamma u : ℝ}
    (hs : 1 < sigma) (hb : beta < 1) (hc : gamma < 1)
    (hgb : 1 - beta ≤ sigma - 1) (hgc : 1 - gamma ≤ sigma - 1) :
    realKernel (sigma - 1) u - realKernel (sigma - beta) u -
      realKernel (sigma - gamma) u ≤ 0 := by
  have h1 := realKernel_half_pole (u := u) (by linarith : 0 < sigma - 1)
    (show sigma - 1 ≤ sigma - beta by linarith)
    (show sigma - beta ≤ 2 * (sigma - 1) by linarith)
  have h2 := realKernel_half_pole (u := u) (by linarith : 0 < sigma - 1)
    (show sigma - 1 ≤ sigma - gamma by linarith)
    (show sigma - gamma ≤ 2 * (sigma - 1) by linarith)
  linarith

theorem lwd_2_23_pole_bracket {sigma beta gamma u : ℝ}
    (hs : 1 < sigma) (hb : beta < 1) (hc : gamma < 1)
    (hgb : 1 - beta ≤ sigma - 1) (hgc : 1 - gamma ≤ sigma - 1) :
    (1 / ((sigma : ℂ) - 1 + I * u)).re -
      (1 / ((sigma : ℂ) - beta + I * u)).re -
      (1 / ((sigma : ℂ) - gamma + I * u)).re ≤ 0 := by
  simpa only [realKernel_eq_inverse_re, Complex.ofReal_sub, Complex.ofReal_one] using
    lwd_G_lemma_two (u := u) hs hb hc hgb hgc

theorem lwd_2_23_constant :
    -0.8973 - 7 * stechkinConductorCoeff * Real.log Real.pi +
      0.3316 * 2 + (5 + Real.sqrt 5) / 10 * 2 + 0.3918 * 4 + 0.0615 ≤ 0.6271 := by
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hroot : Real.sqrt 5 ≤ 2.236068 := by nlinarith [Real.sqrt_nonneg 5]
  have hpi := mul_le_mul lwd_kappa_bounds.1 lwd_log_pi (by norm_num)
    conductorCoeff_bounds.1
  nlinarith only [hroot, hpi]

theorem lwd_2_23_logs {q : ℕ} [NeZero q] {x t u : ℝ}
    (hq : (q : ℝ) ≤ x) (ht : |t| ≤ x / q) (hu : |u| ≤ x / q)
    (ht0 : 0 < |t|) (hu0 : 0 < |u|) :
    Real.log |t| + Real.log |u| + Real.log x +
      2 * Real.log (2 * x) + Real.log (3 * x) ≤
      6 * Real.log x + 2 * Real.log 2 + Real.log 3 := by
  have hx : 0 < x := (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q).trans_le hq
  have hdiv : x / q ≤ x := div_le_self hx.le (by exact_mod_cast NeZero.pos q)
  have h1 := Real.log_le_log ht0 (ht.trans hdiv)
  have h2 := Real.log_le_log hu0 (hu.trans hdiv)
  rw [Real.log_mul (by norm_num) hx.ne', Real.log_mul (by norm_num) hx.ne']
  linarith

theorem lwd_2_23_absorb {x : ℝ} (hx : 8000000000 ≤ x) :
    stechkinConductorCoeff * (2 * Real.log 2 + Real.log 3) + 0.6271 ≤
      stechkinConductorCoeff * Real.log x := by
  have hL := source_log_twenty_two hx
  have hlog : 2 * Real.log 2 + Real.log 3 ≤ 2.5 := by
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have h1 := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  have h2 := mul_le_mul_of_nonneg_left hL conductorCoeff_bounds.1
  linarith [lwd_kappa_bounds.1]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
