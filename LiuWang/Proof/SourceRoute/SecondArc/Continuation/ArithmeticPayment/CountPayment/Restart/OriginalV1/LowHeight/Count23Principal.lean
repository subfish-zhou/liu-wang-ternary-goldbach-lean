import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.Count24Nonprincipal

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def source23Envelope (y : ℝ) : ℝ :=
  y / Real.pi * Real.log y - 0.833 * y + 9.0101 * Real.log y + 56

theorem sourceFive_le_source23 {y : ℝ} (hy : 3.36 ≤ y) :
    Remainder.sourceFiveBound y ≤ source23Envelope y := by
  have hy0 : 0 < y := by linarith
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hnorm : y ≤ ‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
    simpa using Complex.im_le_norm (((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  have hn0 := hy0.trans_le hnorm
  have hnup : ‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ ≤ y + 1 := by
    have he : ‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = (5 / 2 : ℝ) ^ 2 + y ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [Complex.normSq_apply, pow_two]
    nlinarith [norm_nonneg (((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)]
  have hnlog : Real.log (‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ / y) ≤ 1 / y := by
    apply (Real.log_le_sub_one_of_pos (div_pos hn0 hy0)).trans
    apply (le_div_iff₀ hy0).mpr
    rw [sub_mul, div_mul_cancel₀ _ hy0.ne']
    linarith
  have hlogpi : 1.79 ≤ Real.log (2 * Real.pi) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2 * 3)
      (by linarith : (2 * 3 : ℝ) ≤ 2 * Real.pi)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hh
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hcoeff : 0.88 ≤ (1 + Real.log (2 * Real.pi)) / Real.pi := by
    apply (le_div_iff₀ hp).mpr
    linarith [Real.pi_lt_d2]
  have hm : y / Real.pi * Real.log (Real.sqrt ((5 / 4 : ℝ) ^ 2 + (y / 2) ^ 2)) -
      (1 + Real.log Real.pi) / Real.pi * y ≤
        y / Real.pi * Real.log y - 0.88 * y + 0.34 := by
    rw [Remainder.sourceFive_norm_identity]
    have he : Real.log (‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ / 2) =
        Real.log y - Real.log 2 +
          Real.log (‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ / y) := by
      rw [Real.log_div hn0.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_div hn0.ne' hy0.ne']
      ring
    rw [he]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hcoeff
    have hb := mul_le_mul_of_nonneg_left hnlog (div_nonneg hy0.le hp.le)
    have hc := mul_le_mul_of_nonneg_right hcoeff hy0.le
    have ht : y / Real.pi * (1 / y) ≤ 0.34 := by
      field_simp
      linarith [Real.pi_gt_d6]
    simp only [div_eq_mul_inv] at hb hc ht ⊢
    nlinarith only [hb, hc, ht]
  have hc : 10.5 * (2.25 + Real.pi) / Real.pi ≤ 18.0202 := by
    apply (div_le_iff₀ hp).mpr
    linarith [Real.pi_gt_d6]
  have hshift : Real.log (1 + 2 / y) ≤ 0.47 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.47) 5
    norm_num [Finset.sum_range_succ] at he
    have hr : 2 / y ≤ 25 / 42 := (div_le_iff₀ hy0).mpr (by linarith)
    linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hrec : 0.25 / (0.0625 + y ^ 2) ≤ 0.0222 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hbulk : 10.5 * (2.25 + Real.pi) / Real.pi *
      (0.5 * Real.log (2 + y) + 0.25 / (0.0625 + y ^ 2) + 2.6459) ≤
        9.0101 * Real.log y + 18.0202 * (0.235 + 0.0222 + 2.6459) := by
    have he : Real.log (2 + y) = Real.log y + Real.log (1 + 2 / y) := by
      rw [← Real.log_mul hy0.ne' (by positivity)]
      congr 1
      field_simp
      ring
    rw [he]
    apply le_trans (mul_le_mul_of_nonneg_left
      (show 0.5 * (Real.log y + Real.log (1 + 2 / y)) + 0.25 / (0.0625 + y ^ 2) + 2.6459 ≤
        0.5 * Real.log y + 0.235 + 0.0222 + 2.6459 by linarith) (by positivity)) _
    have hh := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤
      0.5 * Real.log y + 0.235 + 0.0222 + 2.6459)
    nlinarith only [hh]
  have hatan : 3 / (2 * Real.pi) * Real.arctan (2 * y / 5) ≤ 0.75 := by
    have hh := mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two (2 * y / 5)).le
      (by positivity : 0 ≤ 3 / (2 * Real.pi))
    have he : 3 / (2 * Real.pi) * (Real.pi / 2) = (0.75 : ℝ) := by field_simp; norm_num
    rwa [he] at hh
  have hsqrt : 2 * y ≤ Real.sqrt (25 + 4 * y ^ 2) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    nlinarith
  have hrec2 : 1 / (2 * Real.sqrt (25 + 4 * y ^ 2)) ≤ 0.075 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hnorm1 : y ≤ ‖(1 : ℂ) + (y : ℂ) * Complex.I‖ := by
    simpa using Complex.im_le_norm ((1 : ℂ) + (y : ℂ) * Complex.I)
  have hrec3 : 1 / ‖(1 : ℂ) + (y : ℂ) * Complex.I‖ ≤ 25 / 84 :=
    (div_le_iff₀ (hy0.trans_le hnorm1)).mpr (by linarith)
  have hrec4 : 1 / y ≤ 25 / 84 := (div_le_iff₀ hy0).mpr (by linarith)
  have hlast : 3 / Real.pi * (0.6105 + 1 / ‖(1 : ℂ) + (y : ℂ) * Complex.I‖ + 1 / y + 1.5 / 4) ≤
      0.956 * (0.6105 + 25 / 42 + 1.5 / 4) := by
    apply mul_le_mul ((div_le_iff₀ hp).mpr (by linarith [Real.pi_gt_d6]))
      (by linarith) (by positivity) (by norm_num)
  unfold Remainder.sourceFiveBound source23Envelope
  linarith only [hm, hbulk, hatan, hrec2, hlast, hy]

theorem count_principal_le_source23 (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 3.36 ≤ y) :
    (DirichletZeroCount.count (1 : Character q) alpha y : ℝ) ≤ source23Envelope y :=
  (Remainder.count_principal_le_sourceFive q ha (by linarith)).trans (sourceFive_le_source23 hy)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
