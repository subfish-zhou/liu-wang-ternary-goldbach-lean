import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.OrdinaryPowers

set_option autoImplicit false

noncomputable section

open Set
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem ordinary_log_log {y : ℝ} (hy : 10000 ≤ y) :
    2 * Real.log (Real.log y) ≤ Real.log y := by
  have hL : 0 < Real.log y := lt_of_lt_of_le (by norm_num) (log_ge_nine hy)
  have h := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div hL.ne' (by norm_num)] at h
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem ordinary_window_majorant {y ξ : ℝ} (hy : 10000 ≤ y)
    (hξ : 1 / 2 ≤ ξ) (hξ1 : ξ ≤ 1) :
    windowMajorant y ξ ≤ 44 * y ^ 2 * Real.log y ^ 4 := by
  have hL := log_ge_nine hy
  have hyp : y ^ (4 * (1 - ξ)) ≤ y ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hlp : Real.log y ^ (8 * ξ - 4) ≤ Real.log y ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hp := mul_le_mul hyp hlp (Real.rpow_nonneg (by linarith) _) (sq_nonneg y)
  have hright : Real.log y ^ 4 ≤ y ^ 2 * Real.log y ^ 4 := by
    have hys : (1 : ℝ) ≤ y ^ 2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hys (by positivity : 0 ≤ Real.log y ^ 4)
  unfold windowMajorant
  nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ Real.log y ^ 4 by positivity)]

theorem ordinary_jensen_numerator {y ξ : ℝ} (hy : 10000 ≤ y)
    (hξ : 1 / 2 ≤ ξ) (hξ1 : ξ ≤ 1) :
    Real.log (2 * (1 + windowMajorant y ξ) / (2 - 8 / (y - 1) ^ 2)) ≤
      5 * Real.log y := by
  have hL := log_ge_nine hy
  have hL0 : 0 < Real.log y := by linarith
  have hy0 : 0 < y := by linarith
  have hfloor : 1 ≤ 2 - 8 / (y - 1) ^ 2 := by
    have h : 8 / (y - 1) ^ 2 ≤ 1 :=
      (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < y - 1))).mpr (by nlinarith)
    linarith
  have hB := windowMajorant_nonneg hy ξ
  have hBbound := ordinary_window_majorant hy hξ hξ1
  have hprod : 1 ≤ y ^ 2 * Real.log y ^ 4 := by
    have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
    have hl4 : (1 : ℝ) ≤ Real.log y ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  have hratio : 2 * (1 + windowMajorant y ξ) / (2 - 8 / (y - 1) ^ 2) ≤
      90 * y ^ 2 * Real.log y ^ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 - 8 / (y - 1) ^ 2)).mpr
    have hm := mul_le_mul_of_nonneg_left hfloor
      (show 0 ≤ 90 * y ^ 2 * Real.log y ^ 4 by positivity)
    nlinarith
  have hl := Real.log_le_log (div_pos (by linarith : 0 < 2 * (1 + windowMajorant y ξ))
    (by linarith : 0 < 2 - 8 / (y - 1) ^ 2)) hratio
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hl
  have h90 := Real.log_le_log (by norm_num : (0 : ℝ) < 90) (by linarith : (90 : ℝ) ≤ y)
  linarith [ordinary_log_log hy]

theorem ordinary_jensen_ratio {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    delta y / 3 ≤ Real.log ((2 - α + 3 * delta y / 2) / (2 - α + delta y)) := by
  have hd := (delta_bounds hy).1
  have hr : 0 < 2 - α + delta y := by linarith
  have hR : 0 < 2 - α + 3 * delta y / 2 := by linarith
  have hRmax : 2 - α + 3 * delta y / 2 ≤ 3 / 2 := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hR hr)
  rw [inv_div] at hl
  have he : 1 - (2 - α + delta y) / (2 - α + 3 * delta y / 2) =
      (delta y / 2) / (2 - α + 3 * delta y / 2) := by
    apply (eq_div_iff hR.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hR.ne']
    ring
  rw [he] at hl
  apply le_trans _ hl
  apply (le_div_iff₀ hR).mpr
  nlinarith

theorem ordinary_jensen_budget {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    Real.log (2 * (1 + windowMajorant y (α - 3 * delta y / 2)) /
      (2 - 8 / (y - 1) ^ 2)) /
        Real.log ((2 - α + 3 * delta y / 2) / (2 - α + delta y)) ≤
      (45 / 2) * Real.log y ^ 2 := by
  have hd := (delta_bounds hy).1
  have hL := log_ge_nine hy
  have hl := ordinary_jensen_ratio hy hα hα1
  have hlog : 0 < Real.log ((2 - α + 3 * delta y / 2) / (2 - α + delta y)) := by linarith
  have hn := ordinary_jensen_numerator hy
    (show 1 / 2 ≤ α - 3 * delta y / 2 by linarith)
    (show α - 3 * delta y / 2 ≤ 1 by linarith)
  have hm := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ (45 / 2 : ℝ) * Real.log y ^ 2 by positivity)
  have hdl := ordinary_delta_log hy
  have hx := congrArg (fun t : ℝ => t * Real.log y) hdl
  apply (div_le_iff₀ hlog).mpr
  nlinarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
