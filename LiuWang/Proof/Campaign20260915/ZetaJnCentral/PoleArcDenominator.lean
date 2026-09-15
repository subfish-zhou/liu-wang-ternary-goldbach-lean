import LiuWang.Proof.Campaign20260915.ZetaJnCentral.CentralCancellation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem hankelDenominator_int_add (k : ℤ) (z : ℂ) :
    rsHankelDenominator (k + z) = rsHankelDenominator z := by
  unfold rsHankelDenominator
  rw [mul_add, exp_add, mul_comm (2 * Real.pi * I) (k : ℂ),
    exp_int_mul_two_pi_mul_I, one_mul]

theorem sine_real_part (z : ℂ) :
    (sin z).re = Real.sin z.re * Real.cosh z.im := by
  simp [Complex.sin, Real.cosh_eq, mul_re, mul_im, exp_im]
  ring

theorem sine_norm_lower (z : ℂ) : |Real.sin z.re| ≤ ‖sin z‖ := by
  have h := abs_re_le_norm (sin z)
  rw [sine_real_part, abs_mul, abs_of_nonneg (zero_le_one.trans (Real.one_le_cosh _))] at h
  have hm := mul_le_mul_of_nonneg_left (Real.one_le_cosh z.im) (abs_nonneg (Real.sin z.re))
  have hm' : |Real.sin z.re| ≤ |Real.sin z.re| * Real.cosh z.im := by simpa using hm
  exact hm'.trans h

theorem hankelDenominator_sine (z : ℂ) :
    rsHankelDenominator z = exp (Real.pi * z * I) * (2 * sin (Real.pi * z)) * I := by
  rw [Complex.two_sin]
  have hp : exp (Real.pi * z * I) * exp (-(Real.pi * z) * I) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2
    ring
  have hq : exp (Real.pi * z * I) * exp (Real.pi * z * I) =
      exp (2 * Real.pi * I * z) := by
    rw [← exp_add]
    congr 1
    ring
  unfold rsHankelDenominator
  calc
    _ = -(exp (Real.pi * z * I) *
        (exp (-(Real.pi * z) * I) - exp (Real.pi * z * I))) := by
      rw [mul_sub, hp, hq]
      ring
    _ = _ := by
      ring_nf
      simp only [I_sq]
      ring

theorem hankelDenominator_re_lower {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    4 * Real.exp (-Real.pi * z.im) * |z.re| ≤ ‖rsHankelDenominator z‖ := by
  have harg : |Real.pi * z.re| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left hz Real.pi_pos.le]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hs' : 2 * |z.re| ≤ |Real.sin (Real.pi * z.re)| := by
    convert hs using 1
    field_simp
  have hn : 2 * |z.re| ≤ ‖sin (Real.pi * z)‖ :=
    hs'.trans (by simpa using sine_norm_lower (Real.pi * z))
  rw [hankelDenominator_sine, norm_mul, norm_mul, norm_mul, norm_I, mul_one,
    norm_ofNat, norm_exp]
  have hr : (Real.pi * z * I).re = -Real.pi * z.im := by
    simp [mul_re, mul_im]
  rw [hr]
  nlinarith [mul_le_mul_of_nonneg_left hn (Real.exp_pos (-Real.pi * z.im)).le]

theorem hankelDenominator_im_lower (z : ℂ) :
    1 - Real.exp (-2 * Real.pi * |z.im|) ≤ ‖rsHankelDenominator z‖ := by
  have h1 := norm_sub_norm_le (1 : ℂ) (exp (2 * Real.pi * I * z))
  have h2 := norm_sub_norm_le (exp (2 * Real.pi * I * z)) (1 : ℂ)
  have hr : (2 * Real.pi * I * z).re = -2 * Real.pi * z.im := by
    simp [mul_re, mul_im]
  rw [norm_one, norm_exp, hr, norm_sub_rev] at h1
  rw [norm_one, norm_exp, hr] at h2
  change 1 - Real.exp (-2 * Real.pi * z.im) ≤ ‖rsHankelDenominator z‖ at h1
  change Real.exp (-2 * Real.pi * z.im) - 1 ≤ ‖rsHankelDenominator z‖ at h2
  rcases le_total 0 z.im with hi | hi
  · simpa only [abs_of_nonneg hi] using h1
  · rw [abs_of_nonpos hi]
    have hp := Real.add_one_le_exp (-2 * Real.pi * z.im)
    have hn := Real.add_one_le_exp (2 * Real.pi * z.im)
    have hx : -2 * Real.pi * -z.im = 2 * Real.pi * z.im := by ring
    rw [hx]
    linarith

def poleArcDenominator (r : ℝ) : ℝ :=
  min (1 - Real.exp (-Real.pi * r)) (2 * r * Real.exp (-Real.pi * r))

theorem poleArcDenominator_pos {r : ℝ} (hr : 0 < r) : 0 < poleArcDenominator r := by
  unfold poleArcDenominator
  apply lt_min
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
  · positivity

theorem pole_circle_denominator {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    {z : ℂ} (hz : ‖z‖ = r) :
    poleArcDenominator r ≤ ‖rsHankelDenominator z‖ := by
  have hre : |z.re| ≤ r := (abs_re_le_norm z).trans_eq hz
  have him : |z.im| ≤ r := (abs_im_le_norm z).trans_eq hz
  by_cases hi : r / 2 ≤ |z.im|
  · apply (min_le_left _ _).trans
    apply (show 1 - Real.exp (-Real.pi * r) ≤
      1 - Real.exp (-2 * Real.pi * |z.im|) by
        have h := Real.exp_le_exp.mpr (show -2 * Real.pi * |z.im| ≤ -Real.pi * r by
          nlinarith [mul_le_mul_of_nonneg_left hi Real.pi_pos.le])
        linarith).trans
    exact hankelDenominator_im_lower z
  · have hnorm : r ≤ |z.re| + |z.im| := by
      rw [← hz]
      exact norm_le_abs_re_add_abs_im z
    have hreal : r / 2 ≤ |z.re| := by linarith
    have he : Real.exp (-Real.pi * r) ≤ Real.exp (-Real.pi * z.im) := by
      apply Real.exp_le_exp.mpr
      nlinarith [le_abs_self z.im, mul_le_mul_of_nonneg_left him Real.pi_pos.le]
    apply (min_le_right _ _).trans
    apply (show 2 * r * Real.exp (-Real.pi * r) ≤
      4 * Real.exp (-Real.pi * z.im) * |z.re| by
        have h := mul_le_mul he hreal (by positivity : 0 ≤ r / 2)
          (Real.exp_pos _).le
        nlinarith).trans
    exact hankelDenominator_re_lower (hre.trans hr1)

def sourcePoleRadius : ℝ := 1 / (2 * Real.sqrt Real.pi)

theorem sourcePoleRadius_pos : 0 < sourcePoleRadius := by
  unfold sourcePoleRadius
  positivity

theorem sourcePoleRadius_lt_half : sourcePoleRadius < 1 / 2 := by
  have hs : 1 < Real.sqrt Real.pi :=
    (Real.lt_sqrt (by norm_num)).mpr (by nlinarith [Real.two_le_pi])
  unfold sourcePoleRadius
  rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.sqrt Real.pi)]
  linarith

theorem source_pole_circle_denominator (k : ℤ) (theta : ℝ) :
    poleArcDenominator sourcePoleRadius ≤
      ‖rsHankelDenominator (circleMap (k : ℂ) sourcePoleRadius theta)‖ := by
  rw [circleMap, hankelDenominator_int_add]
  apply pole_circle_denominator sourcePoleRadius_pos sourcePoleRadius_lt_half.le
  simpa only [circleMap_zero] using
    (norm_circleMap_zero sourcePoleRadius theta).trans (abs_of_pos sourcePoleRadius_pos)

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
