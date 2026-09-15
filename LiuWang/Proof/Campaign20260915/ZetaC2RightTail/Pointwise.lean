import LiuWang.Proof.Campaign20260915.ZetaValidation.SourceC2Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaC2RightTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

def rightTailDenom (eta : ℝ) : ℝ :=
  1 - Real.exp (-(Real.sqrt 2 * Real.pi) * (eta / 2))

def rightTailRate (eta : ℝ) : ℝ := 4 * Real.pi * eta / 11

theorem rightTailDenom_pos {eta : ℝ} (he : 0 < eta) : 0 < rightTailDenom eta := by
  unfold rightTailDenom
  have : -(Real.sqrt 2 * Real.pi) * (eta / 2) < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)
  linarith [Real.exp_lt_one_iff.mpr this]

theorem rightTailRate_pos {eta : ℝ} (he : 0 < eta) : 0 < rightTailRate eta := by
  unfold rightTailRate
  positivity

theorem right_coordinates (eta y : ℝ) :
    (rsDescentPoint eta y).re = eta + y / Real.sqrt 2 ∧
      (rsDescentPoint eta y).im = -y / Real.sqrt 2 := by
  simp [rsDescentPoint, rsDescentDirection]
  constructor <;> ring

theorem right_log_im {eta y : ℝ} (he : 0 < eta) (hy : 0 ≤ y) :
    (rsHankelLog (rsDescentPoint eta y)).im =
      -Real.arctan (y / (y + Real.sqrt 2 * eta)) := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hr : 0 < (rsDescentPoint eta y).re := by
    rw [(right_coordinates eta y).1]
    positivity
  rw [rsHankelLog_eq_principal hr, log_im]
  have h1 := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hr)
  have h2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  rw [← Real.arctan_tan h1 h2, Complex.tan_arg,
    (right_coordinates eta y).1, (right_coordinates eta y).2]
  rw [show -y / Real.sqrt 2 / (eta + y / Real.sqrt 2) =
    -(y / (y + Real.sqrt 2 * eta)) by
      field_simp
      ring, Real.arctan_neg]

theorem right_phase_bound {eta y : ℝ} {m : ℕ}
    (he : 0 < eta) (hy : eta / 2 ≤ y) (hm : eta ≤ (m : ℝ) + 1) :
    (rsSaddleScale * eta) ^ 2 * Real.arctan (y / (y + Real.sqrt 2 * eta)) -
      Real.sqrt 2 * Real.pi * ((m : ℝ) + 1) * y ≤ -rightTailRate eta * y := by
  have hy0 : 0 ≤ y := by linarith
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hslo : 4 / 3 ≤ Real.sqrt 2 := by nlinarith
  have hd : 0 < y + Real.sqrt 2 * eta := by positivity
  have ha : Real.arctan (y / (y + Real.sqrt 2 * eta)) ≤ y / (y + Real.sqrt 2 * eta) := by
    simpa only [Real.tan_arctan] using
      Real.le_tan (Real.arctan_nonneg.mpr (div_nonneg hy0 hd.le))
        (Real.arctan_lt_pi_div_two _)
  have hb : 2 * eta / (y + Real.sqrt 2 * eta) ≤ Real.sqrt 2 - 4 / 11 := by
    rw [div_le_iff₀ hd]
    have hprod := mul_nonneg (show 0 ≤ Real.sqrt 2 - 4 / 11 by linarith)
      (show 0 ≤ y - eta / 2 by linarith)
    have heq : Real.sqrt 2 * (Real.sqrt 2 * eta) = 2 * eta := by
      calc
        _ = Real.sqrt 2 ^ 2 * eta := by ring
        _ = _ := by rw [hs2]
    nlinarith [mul_nonneg he.le (show 0 ≤ Real.sqrt 2 - 4 / 3 by linarith)]
  have hb' := mul_le_mul_of_nonneg_right hb (mul_nonneg Real.pi_pos.le hy0)
  have ha' := mul_le_mul_of_nonneg_left ha (sq_nonneg (rsSaddleScale * eta))
  have hm' := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ Real.sqrt 2 * Real.pi * y by positivity)
  rw [mul_pow, rsSaddleScale_sq] at ha'
  have heq : (2 * eta / (y + Real.sqrt 2 * eta)) * (Real.pi * y) * eta =
      2 * Real.pi * eta ^ 2 * (y / (y + Real.sqrt 2 * eta)) := by ring
  have hb'' := mul_le_mul_of_nonneg_right hb' he.le
  rw [heq] at hb''
  unfold rightTailRate
  rw [mul_pow, rsSaddleScale_sq]
  nlinarith

theorem right_denominator_bound {eta y : ℝ} (hy : eta / 2 ≤ y) :
    rightTailDenom eta * Real.exp (Real.sqrt 2 * Real.pi * y) ≤
      ‖rsHankelDenominator (rsDescentPoint eta y)‖ := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hexp : ‖exp (2 * Real.pi * I * rsDescentPoint eta y)‖ =
      Real.exp (Real.sqrt 2 * Real.pi * y) := by
    rw [norm_exp]
    congr 1
    simp [mul_re, mul_im]
    rw [(right_coordinates eta y).2]
    field_simp
    rw [hs2]
    ring
  have h := norm_sub_norm_le (exp (2 * Real.pi * I * rsDescentPoint eta y)) 1
  rw [hexp, norm_one] at h
  have he' : 1 ≤ Real.exp (Real.sqrt 2 * Real.pi * (y - eta / 2)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have heq : Real.exp (-(Real.sqrt 2 * Real.pi) * (eta / 2)) *
      Real.exp (Real.sqrt 2 * Real.pi * y) =
      Real.exp (Real.sqrt 2 * Real.pi * (y - eta / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold rightTailDenom rsHankelDenominator
  nlinarith [heq]

theorem right_integrand_bound {sigma eta y : ℝ} {m : ℕ}
    (hsigma : sigma ≤ 1) (he : 0 < eta) (hy : eta / 2 ≤ y)
    (hm : eta ≤ (m : ℝ) + 1) :
    ‖rsC2RightIntegrand
      ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m y‖ ≤
      eta ^ (sigma - 1) / rightTailDenom eta * Real.exp (-rightTailRate eta * y) := by
  have hy0 : 0 ≤ y := by linarith
  have hn : eta ≤ ‖rsDescentPoint eta y‖ := by
    have h := re_le_norm (rsDescentPoint eta y)
    rw [(right_coordinates eta y).1] at h
    have : 0 ≤ y / Real.sqrt 2 := by positivity
    linarith
  have hlog : Real.log eta ≤ (rsHankelLog (rsDescentPoint eta y)).re := by
    rw [(rsHankelLog_coordinates_bound _).1]
    exact Real.log_le_log he hn
  have hlog' := mul_le_mul_of_nonpos_left hlog (show sigma - 1 ≤ 0 by linarith)
  have hphase := right_phase_bound he hy hm
  have hnum :
      ‖rsHankelNumerator
        ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) m
        (rsDescentPoint eta y)‖ ≤
        eta ^ (sigma - 1) *
          Real.exp (-rightTailRate eta * y + Real.sqrt 2 * Real.pi * y) := by
    rw [rsHankelNumerator, norm_exp, Real.rpow_def_of_pos he, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp [mul_re, mul_im, pow_two]
    rw [right_log_im he hy0, (right_coordinates eta y).2]
    have heq : 2 * Real.pi * (m : ℝ) * (-y / Real.sqrt 2) =
        -(Real.sqrt 2 * Real.pi * m * y) := by
      have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      field_simp
      rw [hs2]
      ring
    nlinarith [heq]
  have hd := right_denominator_bound hy
  have hdpos : 0 < ‖rsHankelDenominator (rsDescentPoint eta y)‖ :=
    lt_of_lt_of_le (mul_pos (rightTailDenom_pos he) (Real.exp_pos _)) hd
  rw [rsC2RightIntegrand, norm_mul, rsDescentDirection_norm, one_mul,
    rsHankelKernel, norm_div, div_le_iff₀ hdpos]
  calc
    _ ≤ _ := hnum
    _ = (eta ^ (sigma - 1) / rightTailDenom eta * Real.exp (-rightTailRate eta * y)) *
        (rightTailDenom eta * Real.exp (Real.sqrt 2 * Real.pi * y)) := by
      rw [Real.exp_add]
      field_simp [(rightTailDenom_pos he).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (div_nonneg (Real.rpow_nonneg he.le _) (rightTailDenom_pos he).le)
        (Real.exp_pos _).le)

end LiuWang.Proof.Campaign20260915.ZetaC2RightTail
