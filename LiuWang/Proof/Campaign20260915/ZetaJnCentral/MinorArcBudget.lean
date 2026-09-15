import LiuWang.Proof.Campaign20260915.ZetaJnCentral.MinorArcDeformation

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem sourcePoleDistance_lt_one : sourcePoleDistance < 1 := by
  have hs : 1 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpi : Real.sqrt 2 ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt Real.two_le_pi
  unfold sourcePoleDistance sourcePoleRadius
  rw [mul_one_div, div_lt_one (by positivity : 0 < 2 * Real.sqrt Real.pi)]
  linarith

theorem jnCore_source_sphere (sigma : ℝ) {eta R : ℝ} {m : ℕ} {k : ℤ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ)
    {z : ℂ} (hz : ‖z - k‖ = sourcePoleRadius) :
    ‖jnCore sigma eta m N z‖ ≤ poleArcCoreBound sigma eta R N := by
  have hmap : circleMap (k : ℂ) sourcePoleRadius (arg (z - k)) = z := by
    rw [circleMap, ← hz, norm_mul_exp_arg_mul_I]
    ring
  simpa only [hmap] using
    jn_source_pole_pointwise sigma he hR0 hR hDR hk hm0 hm1 N (arg (z - k))

theorem jn_source_minor_integrable (sigma : ℝ) (m N : ℕ) {eta e : ℝ} {k : ℤ}
    (heta : 0 < eta) (hD : sourcePoleDistance < eta) (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) :
    IntervalIntegrable (fun theta : ℝ => sourceMinorVelocity e theta *
      jnCore sigma eta m N (sourceMinorPoint k e theta)) volume
      (-sourceMinorAngle eta k e) (sourceMinorAngle eta k e) := by
  apply ContinuousOn.intervalIntegrable
  have ha := (sourceMinorAngle_mem he hside hk).1
  intro theta ht
  rw [uIcc_of_le (by linarith : -sourceMinorAngle eta k e ≤ sourceMinorAngle eta k e)] at ht
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul (by unfold sourceMinorVelocity; fun_prop)
  exact (sourcePoleCap_analytic sigma m N heta (sourcePoleCap_minor hD he hside hk ht)).continuousAt.comp
    (sourceMinorPoint_deriv k e theta).continuousAt

theorem jn_source_minor_bound (sigma : ℝ) {eta R e : ℝ} {m : ℕ} {k : ℤ}
    (heta : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (he : |e| = 1) (hside : 0 < e * (eta - k))
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖jnSourceMinorArc sigma eta m N k e‖ ≤
      Real.pi * sourcePoleRadius * poleArcCoreBound sigma eta R N := by
  have hB := poleArcCoreBound_nonneg sigma eta hR0 N
  have ha := sourceMinorAngle_mem he hside hk
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -sourceMinorAngle eta k e) (b := sourceMinorAngle eta k e)
    (fun theta _ => show ‖sourceMinorVelocity e theta *
        jnCore sigma eta m N (sourceMinorPoint k e theta)‖ ≤
        sourcePoleRadius * poleArcCoreBound sigma eta R N by
      rw [norm_mul, sourceMinorVelocity_norm he theta]
      exact mul_le_mul_of_nonneg_left
        (jnCore_source_sphere sigma heta hR0 hR hDR hk hm0 hm1 N
          (sourceMinorPoint_radius k he theta)) sourcePoleRadius_pos.le)
  have hlen : |sourceMinorAngle eta k e - -sourceMinorAngle eta k e| ≤ Real.pi := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  apply h.trans
  have hmul := mul_le_mul_of_nonneg_left hlen (mul_nonneg sourcePoleRadius_pos.le hB)
  nlinarith

def sourceMinorHigh (eta : ℝ) (k : ℤ) (e : ℝ) : ℝ :=
  -(eta - k) / Real.sqrt 2 + sourcePoleRadius * Real.sin (sourceMinorAngle eta k e)

def sourceMinorLow (eta : ℝ) (k : ℤ) (e : ℝ) : ℝ :=
  -(eta - k) / Real.sqrt 2 - sourcePoleRadius * Real.sin (sourceMinorAngle eta k e)

theorem sourceMinorLow_le_high {eta e : ℝ} {k : ℤ}
    (he : |e| = 1) (hside : 0 < e * (eta - k))
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) :
    sourceMinorLow eta k e ≤ sourceMinorHigh eta k e := by
  have ha := sourceMinorAngle_mem he hside hk
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ha.1 (by linarith [Real.pi_pos])
  unfold sourceMinorLow sourceMinorHigh
  nlinarith [mul_nonneg sourcePoleRadius_pos.le hs]

theorem jn_source_minor_oriented (sigma : ℝ) (m N : ℕ) {eta e : ℝ} {k : ℤ}
    (heta : 0 < eta) (hD : sourcePoleDistance < eta) (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) :
    (∫ y : ℝ in (sourceMinorHigh eta k e)..(sourceMinorLow eta k e),
      rsJnIntegrand sigma eta m N y) = (e : ℂ) * jnSourceMinorArc sigma eta m N k e := by
  have h := jn_source_minor_deformation sigma m N heta hD he hside hk
  have he' : e = 1 ∨ e = -1 := (abs_eq_abs.mp (by simpa using he : |e| = |(1 : ℝ)|))
  rcases he' with rfl | rfl
  · simpa [sourceMinorY, sourceMinorHigh, sourceMinorLow, Real.sin_neg] using h
  · have hrev : (∫ y : ℝ in (sourceMinorLow eta k (-1))..(sourceMinorHigh eta k (-1)),
        rsJnIntegrand sigma eta m N y) = jnSourceMinorArc sigma eta m N k (-1) := by
      simpa [sourceMinorY, sourceMinorHigh, sourceMinorLow, Real.sin_neg] using h
    rw [ofReal_neg, ofReal_one, neg_one_mul,
      intervalIntegral.integral_symm (sourceMinorLow eta k (-1)) (sourceMinorHigh eta k (-1)), hrev]

theorem jn_source_minor_segment_bound (sigma : ℝ) {eta R e : ℝ} {m : ℕ} {k : ℤ}
    (heta : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (he : |e| = 1) (hside : 0 < e * (eta - k))
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in (sourceMinorHigh eta k e)..(sourceMinorLow eta k e),
      rsJnIntegrand sigma eta m N y‖ ≤
      Real.pi * sourcePoleRadius * poleArcCoreBound sigma eta R N := by
  have hs := rsSaddleScale_pos
  have hD : sourcePoleDistance < eta := by nlinarith
  rw [jn_source_minor_oriented sigma m N heta hD he hside hk, norm_mul, norm_real,
    Real.norm_eq_abs, he, one_mul]
  exact jn_source_minor_bound sigma heta hR0 hR hDR he hside hk hm0 hm1 N

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
