import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.HeightChange

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem sourceSix_le_source24 {q : ℕ} [NeZero q] {y : ℝ} (hy : 3.36 ≤ y) :
    sourceSixBound q y ≤ source24Envelope q y := by
  have hy0 : 0 < y := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hnorm (a : ℝ) : y ≤ ‖(a : ℂ) + (y : ℂ) * Complex.I‖ := by
    simpa using Complex.im_le_norm ((a : ℂ) + (y : ℂ) * Complex.I)
  have hn3 : y ≤ ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ := by simpa using hnorm (3 / 2)
  have hnh : y ≤ ‖(1 / 2 : ℂ) + (y : ℂ) * Complex.I‖ := by simpa using hnorm (1 / 2)
  have hnp : y ≤ ‖(0.5 : ℂ) + (y : ℂ) * Complex.I‖ := by simpa using hnorm 0.5
  have hn2 : y ≤ ‖(2 : ℂ) + (y : ℂ) * Complex.I‖ := by simpa using hnorm 2
  have hn30 := hy0.trans_le hn3
  have hnh0 := hy0.trans_le hnh
  have hnp0 := hy0.trans_le hnp
  have hn20 := hy0.trans_le hn2
  have hnup : ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ ≤ y + 1.5 := by
    have hh := norm_add_le (3 / 2 : ℂ) ((y : ℂ) * Complex.I)
    norm_num [norm_mul, abs_of_pos hy0] at hh ⊢
    linarith
  have hnlog : Real.log (‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / y) ≤ 1.5 / y := by
    apply (Real.log_le_sub_one_of_pos (div_pos hn30 hy0)).trans
    apply (le_div_iff₀ hy0).mpr
    rw [sub_mul, div_mul_cancel₀ _ hy0.ne']
    linarith
  have hlogpi : 1.79 ≤ Real.log (2 * Real.pi) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2 * 3)
      (by linarith : (2 * 3 : ℝ) ≤ 2 * Real.pi)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hh
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hcoeff : 0.874 ≤ (1 + Real.log (2 * Real.pi)) / Real.pi := by
    apply (le_div_iff₀ hp).mpr
    linarith [Real.pi_lt_d2]
  have hm : y / Real.pi *
      Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / (2 * Real.pi)) -
        y / Real.pi ≤ y / Real.pi * Real.log ((q : ℝ) * y) - 0.874 * y + 0.5 := by
    have he : Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / (2 * Real.pi)) =
        Real.log ((q : ℝ) * y) - Real.log (2 * Real.pi) +
          Real.log (‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / y) := by
      rw [Real.log_div (mul_pos hq0 hn30).ne' (by positivity),
        Real.log_mul hq0.ne' hn30.ne', Real.log_mul hq0.ne' hy0.ne',
        Real.log_div hn30.ne' hy0.ne']
      ring
    rw [he]
    have hb := mul_le_mul_of_nonneg_left hnlog (div_nonneg hy0.le hp.le)
    have hc := mul_le_mul_of_nonneg_right hcoeff hy0.le
    have ht : y / Real.pi * (1.5 / y) ≤ 0.5 := by
      field_simp
      linarith
    simp only [div_eq_mul_inv] at hb hc ht ⊢
    nlinarith only [hb, hc, ht]
  have hc : 7 * (1 + 3 / Real.pi) ≤ 13.6846 := by
    field_simp
    linarith [Real.pi_gt_d6]
  have hshift : Real.log (1 + 2 / y) ≤ 0.5 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.5) 3
    norm_num [Finset.sum_range_succ] at he
    have hr : 2 / y ≤ 0.6 := (div_le_iff₀ hy0).mpr (by linarith)
    linarith
  have hlogqy : 0 ≤ Real.log ((q : ℝ) * y) :=
    Real.log_nonneg (by nlinarith)
  have hbulk : 7 * (1 + 3 / Real.pi) *
      (0.5 * Real.log ((q : ℝ) * (2 + y)) + 0.59773) ≤
        6.8423 * Real.log ((q : ℝ) * y) + 13.6846 * (0.25 + 0.59773) := by
    have he : Real.log ((q : ℝ) * (2 + y)) =
        Real.log ((q : ℝ) * y) + Real.log (1 + 2 / y) := by
      rw [← Real.log_mul (mul_pos hq0 hy0).ne' (by positivity)]
      congr 1
      field_simp
      ring
    rw [he]
    have hb := mul_le_mul_of_nonneg_left hshift (by positivity : 0 ≤ 7 * (1 + 3 / Real.pi))
    have hh := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤
      0.5 * Real.log ((q : ℝ) * y) + 0.25 + 0.59773)
    nlinarith only [hb, hh]
  have hatan : 1 / (2 * Real.pi) * Real.arctan (2 * y / 3) ≤ 0.25 := by
    have hh := mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two (2 * y / 3)).le
      (by positivity : 0 ≤ 1 / (2 * Real.pi))
    have he : 1 / (2 * Real.pi) * (Real.pi / 2) = (0.25 : ℝ) := by field_simp; norm_num
    rwa [he] at hh
  have hrec : 1 / (4 * ‖(1 / 2 : ℂ) + (y : ℂ) * Complex.I‖) ≤ 1 / 12 :=
    (div_le_div_iff₀ (mul_pos (by norm_num) hnh0) (by norm_num)).mpr (by linarith)
  have hrec2 : 1.5 /
      (‖(0.5 : ℂ) + (y : ℂ) * Complex.I‖ * ‖(2 : ℂ) + (y : ℂ) * Complex.I‖) ≤ 1 / 6 := by
    apply (div_le_div_iff₀ (mul_pos hnp0 hn20) (by norm_num)).mpr
    nlinarith [mul_le_mul hnp hn2 hy0.le hnp0.le]
  have hlast : 4 / Real.pi * (0.6105 +
      1.5 / (‖(0.5 : ℂ) + (y : ℂ) * Complex.I‖ *
        ‖(2 : ℂ) + (y : ℂ) * Complex.I‖) + 1.5 / 4) ≤
        (4 / 3 : ℝ) * (0.6105 + 1 / 6 + 1.5 / 4) := by
    apply mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3.le)
      (by linarith) (by positivity) (by norm_num)
  unfold sourceSixBound source24Envelope
  linarith only [hm, hbulk, hatan, hrec, hlast]

theorem count_nonprincipal_le_source24 {q : ℕ} [NeZero q]
    {chi : Character q} (hchi : chi ≠ 1) {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 3.36 ≤ y) :
    (DirichletZeroCount.count chi alpha y : ℝ) ≤ source24Envelope q y :=
  (Remainder.count_nonprincipal_le_sourceSix_modulus hchi ha (by linarith)).trans
    (sourceSix_le_source24 hy)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
