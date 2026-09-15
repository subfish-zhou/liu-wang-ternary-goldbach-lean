import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

-- Siegel (1932), equation (18): lambda = sqrt(t), not Brent's tau = t/(2*pi).
def rsSaddleExponent (sigma lambda : ℝ) (z : ℂ) : ℂ :=
  ((sigma - 1 : ℝ) + I * (lambda : ℂ) ^ 2) * log (1 + z / lambda) -
    I * lambda * z + I / 2 * z ^ 2

def rsSaddleWeight (sigma lambda : ℝ) (z : ℂ) : ℂ :=
  exp (rsSaddleExponent sigma lambda z)

theorem rsSaddle_slit {lambda : ℝ} (hl : 0 < lambda) {z : ℂ} (hz : ‖z‖ < lambda) :
    1 + z / (lambda : ℂ) ∈ slitPlane := by
  apply mem_slitPlane_iff.mpr
  left
  simp only [add_re, one_re, div_ofReal_re]
  have hr := (abs_le.mp (abs_re_le_norm z)).1
  have hd : -1 < z.re / lambda := (lt_div_iff₀ hl).mpr (by linarith)
  linarith

theorem rsSaddle_analytic (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    {z : ℂ} (hz : ‖z‖ < lambda) : AnalyticAt ℂ (rsSaddleWeight sigma lambda) z := by
  have hi : AnalyticAt ℂ (fun w : ℂ => 1 + w / lambda) z := by fun_prop
  have hlog : AnalyticAt ℂ (fun w : ℂ => log (1 + w / lambda)) z :=
    hi.clog (rsSaddle_slit hl hz)
  unfold rsSaddleWeight rsSaddleExponent
  exact (analyticAt_const.mul hlog |>.sub (by fun_prop) |>.add (by fun_prop)).cexp

theorem rsSaddle_exponent_deriv (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    {z : ℂ} (hz : ‖z‖ < lambda) :
    HasDerivAt (rsSaddleExponent sigma lambda)
      (((sigma - 1 : ℝ) + I * (lambda : ℂ) ^ 2) / (z + lambda) -
        I * lambda + I * z) z := by
  have hl0 : (lambda : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
  have hs := rsSaddle_slit hl hz
  have hlog := (((hasDerivAt_id z).div_const (lambda : ℂ)).const_add 1).clog hs
  change HasDerivAt (fun w : ℂ => log (1 + w / lambda))
    ((1 / (lambda : ℂ)) / (1 + z / lambda)) z at hlog
  have he : (1 / (lambda : ℂ)) / (1 + z / lambda) = 1 / (z + lambda) := by
    field_simp
    ring
  rw [he] at hlog
  have h := ((hlog.const_mul ((sigma - 1 : ℝ) + I * (lambda : ℂ) ^ 2)).sub
    ((hasDerivAt_id z).const_mul (I * lambda))).add
      (((hasDerivAt_id z).pow 2).const_mul (I / 2))
  simp only [Pi.pow_apply, id_eq, mul_one, pow_one, Nat.cast_ofNat, Nat.reduceSub] at h
  change HasDerivAt (rsSaddleExponent sigma lambda)
    (((sigma - 1 : ℝ) + I * (lambda : ℂ) ^ 2) * (1 / (z + lambda)) -
      I * lambda + I / 2 * (2 * z)) z at h
  convert h using 1
  ring

theorem rsSaddle_differential_equation (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    {z : ℂ} (hz : ‖z‖ < lambda) :
    (z + lambda) * deriv (rsSaddleWeight sigma lambda) z +
      ((1 - sigma : ℝ) - I * z ^ 2) * rsSaddleWeight sigma lambda z = 0 := by
  have hd := (rsSaddle_exponent_deriv sigma hl hz).cexp
  have hn : z + (lambda : ℂ) ≠ 0 := by
    apply ne_zero_of_re_pos
    simp only [add_re, ofReal_re]
    linarith [(abs_le.mp (abs_re_le_norm z)).1]
  rw [show deriv (rsSaddleWeight sigma lambda) z =
    _ by exact hd.deriv]
  unfold rsSaddleWeight
  push_cast
  field_simp
  ring

theorem rsSaddle_zero (sigma lambda : ℝ) : rsSaddleWeight sigma lambda 0 = 1 := by
  simp [rsSaddleWeight, rsSaddleExponent]

theorem rsSaddle_ne_zero (sigma lambda : ℝ) (z : ℂ) : rsSaddleWeight sigma lambda z ≠ 0 :=
  exp_ne_zero _

theorem rsSaddle_first_deriv (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    deriv (rsSaddleWeight sigma lambda) 0 = ((sigma - 1 : ℝ) : ℂ) / lambda := by
  have h := rsSaddle_differential_equation sigma hl (z := 0) (by simpa)
  simp only [zero_add, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero,
    rsSaddle_zero, mul_one] at h
  apply (eq_div_iff (ofReal_ne_zero.mpr hl.ne')).mpr
  push_cast at h ⊢
  linear_combination h

theorem rsSaddle_exponent_rewrite (sigma : ℝ) {lambda : ℝ} (hl : lambda ≠ 0) (z : ℂ) :
    rsSaddleExponent sigma lambda z =
      (sigma - 1 : ℝ) * log (1 + z / lambda) +
        I * (lambda : ℂ) ^ 2 * (log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2) := by
  unfold rsSaddleExponent
  field_simp [ofReal_ne_zero.mpr hl]
  ring

theorem rsSaddle_weight_bound (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    {z : ℂ} (hz : ‖z‖ ≤ lambda / 2) :
    ‖rsSaddleWeight sigma lambda z‖ ≤ Real.exp
      (3 / 2 * |sigma - 1| * ‖z / (lambda : ℂ)‖ +
        2 / 3 * lambda ^ 2 * ‖z / (lambda : ℂ)‖ ^ 3) := by
  have hu : ‖z / (lambda : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl, div_le_iff₀ hl]
    linarith
  have hlog := norm_log_one_add_half_le_self hu
  have htail := norm_log_sub_logTaylor_le 2 (z := z / (lambda : ℂ)) (by linarith)
  have hpoly : logTaylor 3 (z / (lambda : ℂ)) = z / lambda - (z / lambda) ^ 2 / 2 := by
    norm_num [logTaylor, Finset.sum_range_succ]
    ring
  rw [hpoly] at htail
  have htail' : ‖log (1 + z / (lambda : ℂ)) - z / lambda + (z / lambda) ^ 2 / 2‖ ≤
      2 / 3 * ‖z / (lambda : ℂ)‖ ^ 3 := by
    rw [show log (1 + z / (lambda : ℂ)) - z / lambda + (z / lambda) ^ 2 / 2 =
      log (1 + z / lambda) - (z / lambda - (z / lambda) ^ 2 / 2) by ring]
    apply htail.trans
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    have hi : (1 - ‖z / (lambda : ℂ)‖)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hi (pow_nonneg (norm_nonneg (z / (lambda : ℂ))) 3)]
  rw [rsSaddleWeight, norm_exp, Real.exp_le_exp]
  apply (re_le_norm _).trans
  rw [rsSaddle_exponent_rewrite sigma hl.ne']
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_mul, norm_I, one_mul, norm_pow, norm_real,
    norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl]
  have h1 := mul_le_mul_of_nonneg_left hlog (abs_nonneg (sigma - 1))
  have h2 := mul_le_mul_of_nonneg_left htail' (sq_nonneg lambda)
  nlinarith

end LiuWang.Proof.Campaign20260915.ZetaValidation
