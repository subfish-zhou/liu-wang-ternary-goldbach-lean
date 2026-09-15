import LiuWang.Proof.Campaign20260915.ZetaJnCentral.PoleArcDenominator

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

def jnCore (sigma eta : ℝ) (m N : ℕ) (z : ℂ) : ℂ :=
  rsGaussianKernel eta m z *
    rsSaddleRemainder sigma (rsSaddleScale * eta) N (rsSaddleScale * (z - eta))

theorem jnCore_descent (sigma eta y : ℝ) (m N : ℕ) :
    rsDescentDirection * jnCore sigma eta m N (rsDescentPoint eta y) =
      rsJnIntegrand sigma eta m N y := by
  unfold jnCore rsJnIntegrand
  ring

theorem jnCore_analytic (sigma : ℝ) (m N : ℕ) {eta : ℝ} (he : 0 < eta)
    {z : ℂ} (hz : ‖z - eta‖ < eta) (hD : rsHankelDenominator z ≠ 0) :
    AnalyticAt ℂ (jnCore sigma eta m N) z := by
  have hs := rsSaddleScale_pos
  have hg : AnalyticAt ℂ (rsGaussianKernel eta m) z := by
    unfold rsGaussianKernel
    exact (by fun_prop : AnalyticAt ℂ
      (fun z : ℂ => exp (-Real.pi * I * (z - eta) ^ 2 +
        2 * Real.pi * I * (eta - (m : ℝ)) * (z - eta))) z).div
      (rsHankelDenominator_analytic z) hD
  have hw : AnalyticAt ℂ (fun x : ℂ =>
      rsSaddleWeight sigma (rsSaddleScale * eta) (rsSaddleScale * (x - eta))) z :=
    (rsSaddle_analytic sigma (mul_pos hs he) (by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs]
      exact mul_lt_mul_of_pos_left hz hs)).comp (by fun_prop)
  unfold jnCore rsSaddleRemainder
  exact hg.mul (hw.sub (by fun_prop))

def sourcePoleDistance : ℝ := (1 + Real.sqrt 2) * sourcePoleRadius

theorem sourcePoleDistance_pos : 0 < sourcePoleDistance := by
  unfold sourcePoleDistance
  exact mul_pos (by positivity) sourcePoleRadius_pos

theorem source_pole_circle_distance {eta : ℝ} {k : ℤ}
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) (theta : ℝ) :
    ‖circleMap (k : ℂ) sourcePoleRadius theta - eta‖ ≤ sourcePoleDistance := by
  calc
    _ = ‖(circleMap (k : ℂ) sourcePoleRadius theta - k) + ((k : ℂ) - eta)‖ := by
      congr 1
      ring
    _ ≤ ‖circleMap (k : ℂ) sourcePoleRadius theta - k‖ + ‖(k : ℂ) - eta‖ :=
      norm_add_le _ _
    _ = sourcePoleRadius + |eta - k| := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos sourcePoleRadius_pos,
        ← ofReal_intCast, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ _ := by unfold sourcePoleDistance; linarith

theorem gaussian_exponent_disk (eta : ℝ) {m : ℕ} {D : ℝ} {z : ℂ}
    (hz : ‖z - eta‖ ≤ D) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    (-Real.pi * I * (z - eta) ^ 2 +
      2 * Real.pi * I * (eta - (m : ℝ)) * (z - eta)).re ≤
        Real.pi * D ^ 2 + 2 * Real.pi * D := by
  apply (re_le_norm _).trans
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_neg, norm_pow, norm_I, norm_ofNat, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  have hD := (norm_nonneg (z - eta)).trans hz
  have hs := pow_le_pow_left₀ (norm_nonneg (z - eta)) hz 2
  have hm := mul_le_mul hm1 hz (norm_nonneg (z - eta)) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le,
    mul_le_mul_of_nonneg_left hm Real.pi_pos.le]

def poleArcCoreBound (sigma eta R : ℝ) (N : ℕ) : ℝ :=
  (Real.exp (Real.pi * sourcePoleDistance ^ 2 + 2 * Real.pi * sourcePoleDistance) /
      poleArcDenominator sourcePoleRadius) *
    (21 * rsSourceMajorant sigma (rsSaddleScale * eta) R *
      (rsSaddleScale * sourcePoleDistance / R) ^ N)

theorem poleArcCoreBound_nonneg (sigma eta : ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ) :
    0 ≤ poleArcCoreBound sigma eta R N := by
  unfold poleArcCoreBound rsSourceMajorant
  have := rsSaddleScale_pos
  have := sourcePoleDistance_pos
  have := poleArcDenominator_pos sourcePoleRadius_pos
  positivity

theorem jn_source_pole_pointwise (sigma : ℝ) {eta R : ℝ} {m : ℕ} {k : ℤ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) (theta : ℝ) :
    ‖jnCore sigma eta m N (circleMap (k : ℂ) sourcePoleRadius theta)‖ ≤
      poleArcCoreBound sigma eta R N := by
  let z := circleMap (k : ℂ) sourcePoleRadius theta
  have hz : ‖z - eta‖ ≤ sourcePoleDistance := source_pole_circle_distance hk theta
  have hs := rsSaddleScale_pos
  have hnorm : ‖(rsSaddleScale : ℂ) * (z - eta)‖ ≤
      rsSaddleScale * sourcePoleDistance := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hz hs.le
  have hr := rsSaddle_source_remainder_twenty_one sigma (mul_pos hs he) hR0 hR
    (z := (rsSaddleScale : ℂ) * (z - eta)) (by linarith) N
  have hr' : ‖rsSaddleRemainder sigma (rsSaddleScale * eta) N (rsSaddleScale * (z - eta))‖ ≤
      21 * rsSourceMajorant sigma (rsSaddleScale * eta) R *
        (rsSaddleScale * sourcePoleDistance / R) ^ N := by
    apply hr.trans
    apply mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hnorm hR0.le) N)
    unfold rsSourceMajorant
    positivity
  have hd := poleArcDenominator_pos sourcePoleRadius_pos
  have hg : ‖rsGaussianKernel eta m z‖ ≤
      Real.exp (Real.pi * sourcePoleDistance ^ 2 + 2 * Real.pi * sourcePoleDistance) /
        poleArcDenominator sourcePoleRadius := by
    rw [rsGaussianKernel, norm_div, norm_exp]
    exact div_le_div₀ (Real.exp_pos _).le
      (Real.exp_le_exp.mpr (gaussian_exponent_disk eta hz hm0 hm1)) hd
      (source_pole_circle_denominator k theta)
  rw [jnCore, norm_mul]
  exact mul_le_mul hg hr' (norm_nonneg _) (div_nonneg (Real.exp_pos _).le hd.le)

def jnPoleArc (sigma eta : ℝ) (m N : ℕ) (k : ℤ) (a b : ℝ) : ℂ :=
  ∫ theta : ℝ in a..b, (circleMap 0 sourcePoleRadius theta * I) *
    jnCore sigma eta m N (circleMap (k : ℂ) sourcePoleRadius theta)

theorem jn_source_pole_arc_integrable (sigma : ℝ) {eta R : ℝ} (m N : ℕ) {k : ℤ}
    (he : 0 < eta) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) (a b : ℝ) :
    IntervalIntegrable (fun theta : ℝ => (circleMap 0 sourcePoleRadius theta * I) *
      jnCore sigma eta m N (circleMap (k : ℂ) sourcePoleRadius theta)) volume a b := by
  have hs := rsSaddleScale_pos
  have hDeta : sourcePoleDistance < eta := by nlinarith
  apply Continuous.intervalIntegrable
  apply Continuous.mul (by fun_prop)
  rw [continuous_iff_continuousAt]
  intro theta
  apply ContinuousAt.comp (jnCore_analytic sigma m N he
    ((source_pole_circle_distance hk theta).trans_lt hDeta) ?_).continuousAt
    (continuous_circleMap _ _).continuousAt
  exact norm_pos_iff.mp ((poleArcDenominator_pos sourcePoleRadius_pos).trans_le
    (source_pole_circle_denominator k theta))

theorem jn_source_pole_arc_bound (sigma : ℝ) {eta R a b : ℝ} {m : ℕ} {k : ℤ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖jnPoleArc sigma eta m N k a b‖ ≤
      sourcePoleRadius * |b - a| * poleArcCoreBound sigma eta R N := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (fun theta _ => show ‖(circleMap 0 sourcePoleRadius theta * I) *
        jnCore sigma eta m N (circleMap (k : ℂ) sourcePoleRadius theta)‖ ≤
        sourcePoleRadius * poleArcCoreBound sigma eta R N by
      rw [norm_mul, norm_mul, norm_circleMap_zero, abs_of_pos sourcePoleRadius_pos,
        norm_I, mul_one]
      exact mul_le_mul_of_nonneg_left
        (jn_source_pole_pointwise sigma he hR0 hR hDR hk hm0 hm1 N theta)
        sourcePoleRadius_pos.le)
  exact h.trans_eq (by ring)

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
