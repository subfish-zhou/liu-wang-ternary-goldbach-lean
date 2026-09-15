import LiuWang.Proof.GlobalZeroDensity.Strip.Window
import LiuWang.Proof.DirichletZeroCount.Applications.LowAlpha

/-! The auxiliary domain on LWD p.283 and the literal full-line mean (3.42). -/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

theorem source_height_ge_log_six {q : ℕ} [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    10000 * Real.log 6 ≤ y := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  by_cases hq : q ≤ 5
  · have hq5 : (q : ℝ) ≤ 5 := Nat.cast_le.mpr hq
    have hl6 : Real.log 6 ≤ 2 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
    have hdiv : 20000 ≤ 100000 / (q : ℝ) :=
      (le_div_iff₀ hq0).mpr (by linarith)
    linarith [(max_le_iff.mp hy).1]
  · have hq6 : (6 : ℝ) ≤ q := Nat.cast_le.mpr (show 6 ≤ q by omega)
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 6) hq6
    linarith [(max_le_iff.mp hy).2]

theorem sourceDelta_eq_strip_delta (y : ℝ) : sourceDelta y = Strip.delta y := by
  unfold sourceDelta Strip.delta
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num
  ring

theorem source_shift_in_lemma_3_5_domain {y alpha : ℝ}
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1)
    (hy : 10000 * Real.log 6 ≤ y) :
    alpha - sourceDelta y ∈ Icc (1 / 2) (1 - Strip.delta y) := by
  have hy' : 10000 ≤ y := by linarith [Sharp.log_six_ge_one]
  have hlog := log_height_ge_eight hy'
  have hd : 0 < sourceDelta y := by unfold sourceDelta; positivity
  rw [← sourceDelta_eq_strip_delta]
  constructor <;> linarith

theorem weightedMean_eq_original_integral (y sigma : ℝ) :
    weightedMean y sigma =
      ∫ t : ℝ, ‖g y ((sigma : ℂ) + t * I)‖ ^ 2 := by
  unfold weightedMean
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  have hs : (sigma : ℂ) + t * I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
      Complex.one_im] at hi
    exact ht hi
  rw [regularG_eq_g hs]

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
