import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.Elementary

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20

def principalDecimal (y : ℝ) : ℝ :=
  y / Real.pi * Real.log y - 0.833 * y + 9.0101 * Real.log y + 56

def nonprincipalDecimal (Q y : ℝ) : ℝ :=
  y / Real.pi * Real.log (Q * y) - 0.874 * y + 6.8423 * Real.log (Q * y) + 15

theorem log_main_upper {Q a y : ℝ} (hQ : 0 < Q) (hy : 0 < y) :
    y / Real.pi * Real.log (Q * ‖(a : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi)) -
      y / Real.pi ≤
    y / Real.pi * Real.log (Q * y) - (7 / 8) * y + a ^ 2 / (2 * Real.pi * y) := by
  have hn0 : 0 < ‖(a : ℂ) + (y : ℂ) * I‖ :=
    hy.trans_le (norm_ge_height a y)
  have he : Real.log (Q * ‖(a : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi)) =
      Real.log (Q * y) - Real.log (2 * Real.pi) +
        (Real.log ‖(a : ℂ) + (y : ℂ) * I‖ - Real.log y) := by
    rw [Real.log_div (mul_ne_zero hQ.ne' hn0.ne') (by positivity),
      Real.log_mul hQ.ne' hn0.ne', Real.log_mul hQ.ne' hy.ne']
    ring
  have hh := mul_le_mul_of_nonneg_left (log_norm_height (a := a) hy)
    (div_nonneg hy.le Real.pi_pos.le)
  have hneg : 7 / 8 * y ≤ y / Real.pi * (1 + Real.log (2 * Real.pi)) := by
    calc
      _ ≤ (1 + Real.log (2 * Real.pi)) / Real.pi * y :=
        mul_le_mul_of_nonneg_right log_two_pi_payment hy.le
      _ = _ := by ring
  have herror : y / Real.pi * (a ^ 2 / (2 * y ^ 2)) =
      a ^ 2 / (2 * Real.pi * y) := by field_simp
  rw [mul_add, herror] at hh
  rw [he]
  nlinarith

theorem sourceSix_le_decimal {q : ℕ} [NeZero q] {y : ℝ} (hy : 3.36 ≤ y) :
    sourceSixBound q y ≤ nonprincipalDecimal q y := by
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy3 : 3 ≤ y := by linarith
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hl0 : 0 ≤ Real.log ((q : ℝ) * y) := by
    apply Real.log_nonneg
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    nlinarith
  have hm := log_main_upper (a := 3 / 2) hq0 hy0
  norm_num only [ofReal_div, ofReal_ofNat] at hm
  have hn1 : y ≤ ‖(1 / 2 : ℂ) + (y : ℂ) * I‖ := by
    simpa using norm_ge_height (1 / 2) y
  have hn2 : y ≤ ‖(2 : ℂ) + (y : ℂ) * I‖ := by
    simpa using norm_ge_height 2 y
  have hn05 : y ≤ ‖(0.5 : ℂ) + (y : ℂ) * I‖ := by
    simpa using norm_ge_height 0.5 y
  have her : (3 / 2 : ℝ) ^ 2 / (2 * Real.pi * y) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hat : 1 / (2 * Real.pi) * Real.arctan (2 * y / 3) ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two (2 * y / 3)).le
      (by positivity : 0 ≤ 1 / (2 * Real.pi))
    apply hh.trans_eq
    field_simp
    norm_num
  have hr : 1 / (4 * ‖(1 / 2 : ℂ) + (y : ℂ) * I‖) ≤ 1 / 12 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hlog : Real.log ((q : ℝ) * (2 + y)) ≤ Real.log ((q : ℝ) * y) + 0.47 := by
    rw [Real.log_mul hq0.ne' (by positivity), Real.log_mul hq0.ne' hy0.ne']
    linarith [shifted_log hy]
  have hc : 7 * (1 + 3 / Real.pi) / 2 ≤ (6.8423 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hh : 3 / Real.pi ≤ (6.8423 * 2 / 7 - 1 : ℝ) := by
      apply (div_le_iff₀ hp).mpr
      linarith [Real.pi_gt_d6]
    linarith
  have hc14 : 7 * (1 + 3 / Real.pi) ≤ (14 : ℝ) := by
    have hh : 3 / Real.pi ≤ 1 := (div_le_one hp).mpr hp3.le
    linarith
  have hfee : 7 * (1 + 3 / Real.pi) *
      (0.5 * Real.log ((q : ℝ) * (2 + y)) + 0.59773) ≤
      6.8423 * Real.log ((q : ℝ) * y) + 14 * (0.235 + 0.59773) := by
    have h1 := mul_le_mul_of_nonneg_left hlog
      (by positivity : 0 ≤ 7 * (1 + 3 / Real.pi) / 2)
    have h2 := mul_le_mul_of_nonneg_right hc hl0
    have h3 := mul_le_mul_of_nonneg_right hc14
      (by norm_num : (0 : ℝ) ≤ 0.235 + 0.59773)
    nlinarith
  have hprod : 9 ≤ ‖(0.5 : ℂ) + (y : ℂ) * I‖ * ‖(2 : ℂ) + (y : ℂ) * I‖ := by
    nlinarith
  have hrec : 1.5 / (‖(0.5 : ℂ) + (y : ℂ) * I‖ *
      ‖(2 : ℂ) + (y : ℂ) * I‖) ≤ 1 / 6 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hlast : 4 / Real.pi * (0.6105 +
      1.5 / (‖(0.5 : ℂ) + (y : ℂ) * I‖ * ‖(2 : ℂ) + (y : ℂ) * I‖) + 1.5 / 4) ≤
      (4 / 3 : ℝ) * (0.6105 + 1 / 6 + 1.5 / 4) :=
    mul_le_mul (by apply (div_le_iff₀ hp).mpr; linarith) (by linarith)
      (by positivity) (by norm_num)
  unfold sourceSixBound nonprincipalDecimal
  nlinarith

theorem sourceFive_le_decimal {y : ℝ} (hy : 3.36 ≤ y) :
    sourceFiveBound y ≤ principalDecimal y := by
  have hy0 : 0 < y := by linarith
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hl0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hm := log_main_upper (Q := 1) (a := 5 / 2) (by norm_num) hy0
  norm_num only [ofReal_div, ofReal_ofNat] at hm
  have hn0 : 0 < ‖(5 / 2 : ℂ) + (y : ℂ) * I‖ :=
    hy0.trans_le (by simpa using norm_ge_height (5 / 2) y)
  have he : y / Real.pi * Real.log (Real.sqrt ((5 / 4 : ℝ) ^ 2 + (y / 2) ^ 2)) -
      (1 + Real.log Real.pi) / Real.pi * y =
      y / Real.pi * Real.log (1 * ‖(5 / 2 : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi)) -
        y / Real.pi := by
    rw [sourceFive_norm_identity]
    norm_num only [ofReal_div, ofReal_ofNat]
    simp only [one_mul]
    rw [Real.log_div hn0.ne' (by norm_num), Real.log_div hn0.ne' (by positivity),
      Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  rw [← he, one_mul] at hm
  have her : (5 / 2 : ℝ) ^ 2 / (2 * Real.pi * y) ≤ 625 / 2016 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hat : 3 / (2 * Real.pi) * Real.arctan (2 * y / 5) ≤ 3 / 4 := by
    have hh := mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two (2 * y / 5)).le
      (by positivity : 0 ≤ 3 / (2 * Real.pi))
    apply hh.trans_eq
    field_simp
    norm_num
  have hsqrt : 2 * y ≤ Real.sqrt (25 + 4 * y ^ 2) := by
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr (by nlinarith)
  have hr : 1 / (2 * Real.sqrt (25 + 4 * y ^ 2)) ≤ 25 / 336 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hrec : 0.25 / (0.0625 + y ^ 2) ≤ 625 / 28224 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hc : 10.5 * (2.25 + Real.pi) / Real.pi ≤ (18.0202 : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    linarith [Real.pi_gt_d6]
  have hfee : 10.5 * (2.25 + Real.pi) / Real.pi *
      (0.5 * Real.log (2 + y) + 0.25 / (0.0625 + y ^ 2) + 2.6459) ≤
      9.0101 * Real.log y + 18.0202 * (0.235 + 625 / 28224 + 2.6459) := by
    have hh := mul_le_mul hc (show
        0.5 * Real.log (2 + y) + 0.25 / (0.0625 + y ^ 2) + 2.6459 ≤
          0.5 * Real.log y + 0.235 + 625 / 28224 + 2.6459 by
        linarith [shifted_log hy])
      (by have hh := Real.log_nonneg (by linarith : 1 ≤ 2 + y); positivity)
      (by norm_num : (0 : ℝ) ≤ 18.0202)
    nlinarith
  have hiy : 1 / y ≤ (25 / 84 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith
  have hir := (reciprocal_norm (a := 1) hy0).trans hiy
  norm_num only [ofReal_one] at hir
  have hlast : 3 / Real.pi * (0.6105 +
      1 / ‖(1 : ℂ) + (y : ℂ) * I‖ + 1 / y + 1.5 / 4) ≤
      (0.6105 + 25 / 84 + 25 / 84 + 1.5 / 4 : ℝ) := by
    apply le_trans (mul_le_mul (by exact (div_le_one hp).mpr hp3.le)
      (by linarith : _ ≤ (0.6105 + 25 / 84 + 25 / 84 + 1.5 / 4 : ℝ))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1))
    rw [one_mul]
  unfold sourceFiveBound principalDecimal
  nlinarith

theorem principal_count_decimal (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 1 / 2 ≤ alpha) (hy : 3.36 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤ principalDecimal y :=
  (count_principal_le_sourceFive q (by linarith) (by linarith)).trans
    (sourceFive_le_decimal hy)

theorem nonprincipal_count_decimal {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 1 / 2 ≤ alpha) (hy : 3.36 ≤ y) :
    (count chi alpha y : ℝ) ≤ nonprincipalDecimal q y :=
  (count_nonprincipal_le_sourceSix_modulus hchi (by linarith) (by linarith)).trans
    (sourceSix_le_decimal hy)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20
