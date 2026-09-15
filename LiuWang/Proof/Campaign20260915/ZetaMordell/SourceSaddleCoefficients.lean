import LiuWang.Proof.Campaign20260915.ZetaMordell.SourcePhiBridge
import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelSaddleRecurrence

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem sourceSaddle_scaled_zero (sigma eta : ℝ) :
    rsSaddleCoefficient sigma (rsSaddleScale * eta) 0 * (rsSaddleScale : ℂ) ^ 0 = 1 := by
  simp [rsSaddle_coefficient_zero]

theorem sourceSaddle_scaled_one {eta : ℝ} (he : 0 < eta) :
    rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 1 * (rsSaddleScale : ℂ) ^ 1 =
      -1 / (2 * (eta : ℂ)) := by
  rw [rsSaddle_coefficient_one (1 / 2) (mul_pos rsSaddleScale_pos he)]
  push_cast
  have hc := ofReal_ne_zero.mpr rsSaddleScale_pos.ne'
  have heC := ofReal_ne_zero.mpr he.ne'
  field_simp
  ring

theorem sourceSaddle_scaled_two {eta : ℝ} (he : 0 < eta) :
    rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 2 * (rsSaddleScale : ℂ) ^ 2 =
      3 / (8 * (eta : ℂ) ^ 2) := by
  rw [rsSaddle_coefficient_two (1 / 2) (mul_pos rsSaddleScale_pos he)]
  push_cast
  have hc := ofReal_ne_zero.mpr rsSaddleScale_pos.ne'
  have heC := ofReal_ne_zero.mpr he.ne'
  field_simp
  ring

theorem sourceSaddle_scaled_recurrence (sigma : ℝ) {eta : ℝ} (he : 0 < eta) (n : ℕ) :
    ((n + 3 : ℕ) : ℂ) * eta *
        (rsSaddleCoefficient sigma (rsSaddleScale * eta) (n + 3) * (rsSaddleScale : ℂ) ^ (n + 3)) =
      -(((n + 3 : ℕ) : ℂ) - sigma) *
        (rsSaddleCoefficient sigma (rsSaddleScale * eta) (n + 2) * (rsSaddleScale : ℂ) ^ (n + 2)) +
      (2 * Real.pi * I) *
        (rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n) := by
  have h := rsSaddle_coefficient_recurrence sigma (mul_pos rsSaddleScale_pos he) n
  have hs : (rsSaddleScale : ℂ) ^ 2 = 2 * Real.pi := by exact_mod_cast rsSaddleScale_sq
  push_cast at h ⊢
  calc
    _ = (rsSaddleScale : ℂ) ^ (n + 2) *
      (((n + 3 : ℕ) : ℂ) * (rsSaddleScale * eta) *
        rsSaddleCoefficient sigma (rsSaddleScale * eta) (n + 3)) := by
      push_cast
      rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
      ring
    _ = _ := by
      push_cast
      rw [h, pow_add (rsSaddleScale : ℂ) n 2, hs]
      ring

theorem sourceSaddle_scaled_three {eta : ℝ} (he : 0 < eta) :
    rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 3 * (rsSaddleScale : ℂ) ^ 3 =
      2 * Real.pi * I / (3 * eta) - 5 / (16 * (eta : ℂ) ^ 3) := by
  have h := sourceSaddle_scaled_recurrence (1 / 2) he 0
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, ofReal_div, ofReal_one, ofReal_ofNat] at h
  rw [sourceSaddle_scaled_zero, sourceSaddle_scaled_two he] at h
  have heC := ofReal_ne_zero.mpr he.ne'
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (3 : ℂ) ≠ 0) heC)
  rw [h]
  field_simp
  ring

theorem sourceSaddle_scaled_four {eta : ℝ} (he : 0 < eta) :
    rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 4 * (rsSaddleScale : ℂ) ^ 4 =
      -(5 * Real.pi * I) / (6 * (eta : ℂ) ^ 2) + 35 / (128 * (eta : ℂ) ^ 4) := by
  have h := sourceSaddle_scaled_recurrence (1 / 2) he 1
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, ofReal_div, ofReal_one, ofReal_ofNat] at h
  rw [sourceSaddle_scaled_three he, sourceSaddle_scaled_one he] at h
  have heC := ofReal_ne_zero.mpr he.ne'
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) heC)
  rw [h]
  field_simp
  ring

theorem sourceSaddle_scaled_five {eta : ℝ} (he : 0 < eta) :
    rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 5 * (rsSaddleScale : ℂ) ^ 5 =
      9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) - 63 / (256 * (eta : ℂ) ^ 5) := by
  have h := sourceSaddle_scaled_recurrence (1 / 2) he 2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, ofReal_div, ofReal_one, ofReal_ofNat] at h
  rw [sourceSaddle_scaled_four he, sourceSaddle_scaled_two he] at h
  have heC := ofReal_ne_zero.mpr he.ne'
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (5 : ℂ) ≠ 0) heC)
  rw [h]
  field_simp
  ring

theorem sourceSaddle_scaled_six {eta : ℝ} (he : 0 < eta) :
    rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 6 * (rsSaddleScale : ℂ) ^ 6 =
      -(2 * Real.pi ^ 2) / (9 * (eta : ℂ) ^ 2) -
        223 * Real.pi * I / (240 * (eta : ℂ) ^ 4) + 231 / (1024 * (eta : ℂ) ^ 6) := by
  have h := sourceSaddle_scaled_recurrence (1 / 2) he 3
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, ofReal_div, ofReal_one, ofReal_ofNat] at h
  rw [sourceSaddle_scaled_five he, sourceSaddle_scaled_three he] at h
  have heC := ofReal_ne_zero.mpr he.ne'
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (6 : ℂ) ≠ 0) heC)
  rw [h]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end LiuWang.Proof.Campaign20260915.ZetaMordell
