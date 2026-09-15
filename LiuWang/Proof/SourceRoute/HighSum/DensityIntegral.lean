import LiuWang.Proof.SourceRoute.HighSum.HeightAlpha
import LiuWang.Proof.DirichletZeroCount.Applications.LowAlpha

/-! # Integrating the literal Theorem 7 expression, main paper (2.24)

This is a scalar theorem about the published density formula, not a proof of
the missing high-alpha family density estimate.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum

theorem integral_exp_shift (a b : ℝ) {t : ℝ} (ht : t ≠ 0) :
    (∫ alpha in a..b, Real.exp (t * (alpha - 1))) =
      (Real.exp (t * (b - 1)) - Real.exp (t * (a - 1))) / t := by
  rw [intervalIntegral.integral_comp_sub_right
    (fun x => Real.exp (t * x)) 1,
    intervalIntegral.integral_comp_mul_left Real.exp ht, integral_exp]
  simp only [smul_eq_mul, div_eq_inv_mul]

theorem weighted_power_product {N : ℕ} (hN : 0 < N) {A : ℝ} (hA : 0 < A)
    (alpha : ℝ) :
    (N : ℝ) ^ (alpha - 1) * A ^ (1 - alpha) =
      Real.exp ((sourceL N - Real.log A) * (alpha - 1)) := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hN), Real.rpow_def_of_pos hA,
    ← Real.exp_add]
  congr 1
  unfold sourceL
  ring

def sevenEnvelope (N q : ℕ) (y alpha : ℝ) : ℝ :=
  16541 * Real.log y ^ (6 : ℕ) * sourceL N *
      Real.exp (sourceL N * (alpha - 1)) +
    (17102 + 254231 / Real.log ((q : ℝ) * y)) *
      Real.log ((q : ℝ) * y) ^ (6 : ℕ) * sourceL N *
        Real.exp ((sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) *
          (alpha - 1))

theorem continuous_sevenEnvelope (N q : ℕ) (y : ℝ) :
    Continuous (sevenEnvelope N q y) := by
  unfold sevenEnvelope
  fun_prop

theorem sourceSeven_weighted_le_envelope {N q : ℕ} [NeZero q]
    (hN : 1 ≤ (N : ℝ)) {y alpha : ℝ} (hy : 0 < y)
    (hs : 1 ≤ Real.log ((q : ℝ) * y)) (ha : alpha ≤ 1) :
    layerKernel N alpha * Applications.sourceSevenBound q alpha y ≤
      sevenEnvelope N q y alpha := by
  have hn : 0 < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hA : 0 < (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) := by
    have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    positivity
  have hp : Real.log ((q : ℝ) * y) ^ (6 * alpha) ≤
      Real.log ((q : ℝ) * y) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hs (by norm_num only [Nat.cast_ofNat]; linarith)
  have hc : 0 ≤ (N : ℝ) ^ (alpha - 1) * sourceL N *
      (17102 + 254231 / Real.log ((q : ℝ) * y)) *
        ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) := by
    have hL : 0 ≤ sourceL N := Real.log_nonneg hN
    positivity
  have h := mul_le_mul_of_nonneg_left hp hc
  unfold layerKernel Applications.sourceSevenBound
  calc
    _ ≤ 16541 * Real.log y ^ (6 : ℕ) * sourceL N * (N : ℝ) ^ (alpha - 1) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          Real.log ((q : ℝ) * y) ^ (6 : ℕ) * sourceL N *
            ((N : ℝ) ^ (alpha - 1) *
              ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha)) := by
      nlinarith only [h]
    _ = _ := by
      rw [weighted_power_product hn hA, Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
      rfl

theorem integral_sevenEnvelope {N q : ℕ} (y a b : ℝ)
    (hL : sourceL N ≠ 0)
    (hD : sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ≠ 0) :
    (∫ alpha in a..b, sevenEnvelope N q y alpha) =
      16541 * Real.log y ^ (6 : ℕ) *
        (Real.exp (sourceL N * (b - 1)) - Real.exp (sourceL N * (a - 1))) +
      ((17102 + 254231 / Real.log ((q : ℝ) * y)) *
        Real.log ((q : ℝ) * y) ^ (6 : ℕ) * sourceL N /
          (sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)))) *
        (Real.exp ((sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) *
          (b - 1)) -
        Real.exp ((sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) *
          (a - 1))) := by
  unfold sevenEnvelope
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul, integral_exp_shift a b hL,
    integral_exp_shift a b hD]
  field_simp

theorem sourceSeven_integrand_integrable {N q : ℕ} [NeZero q]
    (hN : 0 < N) {y : ℝ} (hy : 0 < y) (hs : 0 < Real.log ((q : ℝ) * y))
    (a b : ℝ) :
    IntervalIntegrable (fun alpha =>
      layerKernel N alpha * Applications.sourceSevenBound q alpha y) volume a b := by
  have hA : 0 < (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) := by
    have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    positivity
  have hAp := hA.ne'
  have hsp := hs.ne'
  apply Continuous.intervalIntegrable
  unfold Applications.sourceSevenBound
  exact (continuous_layerKernel hN).mul (by fun_prop)

theorem sourceSeven_integral_le_source24 {N q : ℕ} [NeZero q]
    (hN : 1 < (N : ℝ)) {y : ℝ} (hy : 0 < y)
    (hs : 1 ≤ Real.log ((q : ℝ) * y))
    (hD : 0 < sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)))
    (hb : (19 / 20 : ℝ) ≤ 1 - 0.478 / Real.log ((q : ℝ) * y)) :
    (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * Applications.sourceSevenBound q alpha y) ≤
      (17102 + 254231 / Real.log ((q : ℝ) * y)) *
        Real.log ((q : ℝ) * y) ^ (6 : ℕ) * sourceL N /
          (sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) *
        Real.exp (-0.478 *
          (sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) /
            Real.log ((q : ℝ) * y)) +
      16541 * Real.log y ^ (6 : ℕ) *
        Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) := by
  have hn : 0 < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hL : 0 < sourceL N := Real.log_pos hN
  have hs0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  have hb1 : 1 - 0.478 / Real.log ((q : ℝ) * y) ≤ 1 := by
    have : 0 ≤ (0.478 : ℝ) / Real.log ((q : ℝ) * y) := by positivity
    linarith
  calc
    _ ≤ ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        sevenEnvelope N q y alpha := by
      apply intervalIntegral.integral_mono_on hb
        (sourceSeven_integrand_integrable hn hy hs0 _ _)
        ((continuous_sevenEnvelope N q y).intervalIntegrable _ _)
      intro alpha ha
      exact sourceSeven_weighted_le_envelope hN.le hy hs (ha.2.trans hb1)
    _ ≤ _ := by
      rw [integral_sevenEnvelope _ _ _ hL.ne' hD.ne']
      have he (t : ℝ) :
          t * (1 - 0.478 / Real.log ((q : ℝ) * y) - 1) =
            -0.478 * t / Real.log ((q : ℝ) * y) := by ring
      simp only [he]
      have hc : 0 ≤ (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          Real.log ((q : ℝ) * y) ^ (6 : ℕ) * sourceL N /
            (sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) := by positivity
      have hc' : 0 ≤ 16541 * Real.log y ^ (6 : ℕ) := by positivity
      nlinarith [mul_nonneg hc (Real.exp_pos
        ((sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) *
          ((19 / 20 : ℝ) - 1))).le,
        mul_nonneg hc' (Real.exp_pos (sourceL N * ((19 / 20 : ℝ) - 1))).le]

end LiuWang.Proof.SourceRoute.HighSum
