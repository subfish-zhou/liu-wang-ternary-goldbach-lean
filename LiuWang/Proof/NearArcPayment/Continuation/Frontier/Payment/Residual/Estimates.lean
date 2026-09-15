import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Regression

/-! 原 lastCost 实零余族的窗权与原高度零锐计数；不添加实部付款上截带。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual

open Interfaces Parameters CompleteExpansion DirichletZeroCount

def realModulusLimit (N : ℕ) : ℝ := sourceL N ^ 2 / 400

theorem log_3100_le_nine : Real.log 3100 ≤ 9 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have hh := Real.quadratic_le_exp_of_nonneg (x := 9 / 8) (by norm_num)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 9 / 8 + (9 / 8) ^ 2 / 2) hh 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

theorem log_square_bound {x : ℝ} (hx : 3100 ≤ x) :
    (Real.log x) ^ 2 ≤ 81 * x / 3100 := by
  have hx0 : 0 < x := by linarith
  have hs1 : 1 ≤ Real.sqrt (x / 3100) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    linarith
  have he : Real.log x = Real.log 3100 + 2 * Real.log (Real.sqrt (x / 3100)) := by
    rw [Real.log_sqrt (by positivity), Real.log_div hx0.ne' (by norm_num)]
    ring
  have hl : Real.log x ≤ 9 * Real.sqrt (x / 3100) := by
    rw [he]
    linarith [log_3100_le_nine, Real.log_le_sub_one_of_pos
      (Real.sqrt_pos.mpr (by positivity : 0 < x / 3100))]
  have hn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ x / 3100)]

theorem window_log_lower {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    sourceL N - 8 ≤ Real.log (0.001 * (N : ℝ)) := by
  have hn := natCast_pos_of_exp_le hN
  have he : (1000 : ℝ) ≤ Real.exp 8 := by
    have hh := Real.quadratic_le_exp_of_nonneg (x := 1) (by norm_num)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 1 + 1 ^ 2 / 2) hh 8
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have hl : Real.log 1000 ≤ 8 := (Real.log_le_iff_le_exp (by norm_num)).mpr he
  have heq : Real.log (0.001 : ℝ) = -Real.log 1000 := by
    rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [Real.log_mul (by norm_num : (0.001 : ℝ) ≠ 0) hn.ne', heq]
  change sourceL N - 8 ≤ -Real.log 1000 + sourceL N
  linarith

theorem left_real_weight {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {beta : ℝ} (hb : beta ≤ realAlpha N) :
    (0.001 * (N : ℝ)) ^ (beta - 1) ≤ 1 / sourceL N ^ 2 := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hlog : 0 < Real.log (sourceL N) := Real.log_pos (by linarith [sourceL_ge_3100 hN])
  have hw := sourceWindow_gt_one hN0
  have hlw : 0 < Real.log (0.001 * (N : ℝ)) := Real.log_pos hw
  have hprod : 8 * Real.log (sourceL N) ^ 2 ≤
      0.27 * Real.log (0.001 * (N : ℝ)) := by
    have hs := log_square_bound (sourceL_ge_3100 hN)
    have hl := window_log_lower hN
    nlinarith [sourceL_ge_3100 hN]
  have hexp : Real.log (0.001 * (N : ℝ)) * (beta - 1) ≤
      -(2 * Real.log (sourceL N)) := by
    have ha : beta - 1 ≤ -(0.27 / (4 * Real.log (sourceL N))) := by
      simp only [realAlpha, realScale, Real.log_pow, Nat.cast_ofNat] at hb
      linarith
    have hh := mul_le_mul_of_nonneg_left ha hlw.le
    have hd : 2 * Real.log (sourceL N) ≤
        0.27 * Real.log (0.001 * (N : ℝ)) / (4 * Real.log (sourceL N)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [hprod]
    have he : Real.log (0.001 * (N : ℝ)) * -(0.27 / (4 * Real.log (sourceL N))) =
        -(0.27 * Real.log (0.001 * (N : ℝ)) / (4 * Real.log (sourceL N))) := by ring
    rw [he] at hh
    linarith
  rw [Real.rpow_def_of_pos (by linarith : 0 < 0.001 * (N : ℝ))]
  calc
    _ ≤ Real.exp (-(2 * Real.log (sourceL N))) := Real.exp_le_exp.mpr hexp
    _ = _ := by
      rw [Real.exp_neg, show 2 * Real.log (sourceL N) = Real.log (sourceL N ^ 2) by
        rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hL 2)]
      simp only [one_div]

theorem real_modulus_domain {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ realModulusLimit N) :
    100000000000 ≤ realScale N ∧ (q : ℝ) * max 1 (0 : ℝ) ≤ realScale N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hl := sourceL_ge_3100 hN
  have hs : sourceL N ^ 2 / 400 ≤ sourceL N ^ 4 := by
    have hh : 1 ≤ sourceL N ^ 2 := one_le_pow₀ (by linarith : 1 ≤ sourceL N)
    nlinarith [sq_nonneg (sourceL N ^ 2)]
  constructor
  · exact (by norm_num : (100000000000 : ℝ) ≤ 3100 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) hl 4)
  · simpa only [realScale, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), mul_one] using hq.trans hs

theorem sharp_zero_height {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ realModulusLimit N) (chi : Character q) :
    sharpCount chi 0 ≤ sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlogq : Real.log q ≤ sourceL N / 8 := by
    have hqL : (q : ℝ) ≤ sourceL N ^ 2 := by
      unfold realModulusLimit at hq
      nlinarith [sq_nonneg (sourceL N)]
    have hh := Real.log_le_log hq0 hqL
    rw [Real.log_pow] at hh
    have hl := nat_mul_log_lt (sourceL_ge_2000 (exp_2000_le_of_exp_3100_le hN))
      (k := 16) (by norm_num)
    norm_num at hh hl
    linarith
  have hl2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hL3100 := sourceL_ge_3100 hN
  unfold sharpCount
  split_ifs
  · apply (min_le_right _ _).trans
    unfold Remainder.uniformXiCountBound Remainder.uniformXiFee Remainder.sourceGammaMain
    simp only [zero_mul, zero_div, Real.arctan_zero, mul_zero, sub_zero, abs_zero, zero_add]
    apply (div_le_iff₀ Real.pi_pos).mpr
    have hp : 0 ≤ 5 * Real.pi / 2 + 4 := by positivity
    have hh := mul_le_mul_of_nonneg_left hl2 hp
    nlinarith [mul_nonneg (by linarith : 0 ≤ sourceL N) (by linarith : 0 ≤ Real.pi - 3)]
  · apply (min_le_right _ _).trans
    apply (Remainder.uniformCountBound_mono_modulus
      (Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) (by norm_num)).trans
    unfold Remainder.uniformCountBound Remainder.uniformHorizontalFee Remainder.sourceGammaMain
    simp only [zero_mul, zero_div, Real.arctan_zero, mul_zero, sub_zero, abs_zero, zero_add, add_zero]
    apply (div_le_iff₀ Real.pi_pos).mpr
    have hp : 0 ≤ 5 * Real.pi / 2 + 4 := by positivity
    have hh := mul_le_mul_of_nonneg_left hlogq hp
    have hh2 := mul_le_mul_of_nonneg_left hl2 hp
    nlinarith [mul_nonneg (by linarith : 0 ≤ sourceL N) (by linarith : 0 ≤ Real.pi - 3),
      mul_nonneg (by linarith : 0 ≤ sourceL N) (by linarith : 0 ≤ 4 - Real.pi)]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual
