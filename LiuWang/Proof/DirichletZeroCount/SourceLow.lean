import LiuWang.Proof.DirichletZeroCount.Family

/-!
# Companion Theorem 6: its literal bound on the closed low-height branch

The unrestricted source theorem is not asserted here. This proves its actual
right-hand side for `0 <= y <= 1`, including real zeros and imprimitive
characters, by a stronger moving-kernel count instead of numerical zero tables.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.DirichletZeroCount

def sourceSixBound (q : ℕ) (y : ℝ) : ℝ :=
  y / Real.pi *
      Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / (2 * Real.pi)) -
    y / Real.pi + 1 / (2 * Real.pi) * Real.arctan (2 * y / 3) +
    1 / (4 * ‖(1 / 2 : ℂ) + (y : ℂ) * Complex.I‖) + 1 +
    7 * (1 + 3 / Real.pi) * (0.5 * Real.log ((q : ℝ) * (2 + y)) + 0.59773) +
    4 / Real.pi * (0.6105 +
      1.5 / (‖(0.5 : ℂ) + (y : ℂ) * Complex.I‖ *
        ‖(2 : ℂ) + (y : ℂ) * Complex.I‖) + 1.5 / 4)

theorem sourceSixBound_low_lower {q : ℕ} (hq : 3 ≤ q)
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    6 * Real.log q + 54 / 5 ≤ sourceSixBound q y := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hpi0 := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hn : (3 / 2 : ℝ) ≤ ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ := by
    simpa using Complex.re_le_norm ((3 / 2 : ℂ) + (y : ℂ) * Complex.I)
  have hratio : (1 / 2 : ℝ) ≤
      (q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hlog : -1 ≤ Real.log
      ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / (2 * Real.pi)) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hratio
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [one_div, Real.log_inv] at hh
    linarith
  have hyp : 0 ≤ y / Real.pi := div_nonneg hy hpi0.le
  have hyp1 : y / Real.pi ≤ 1 / 2 := by
    apply (div_le_iff₀ hpi0).mpr
    linarith
  have hmain : -1 ≤ y / Real.pi *
      Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * Complex.I‖ / (2 * Real.pi)) -
        y / Real.pi := by
    have h := mul_le_mul_of_nonneg_left hlog hyp
    nlinarith
  have hl2 : Real.log q + 2 / 3 ≤ Real.log ((q : ℝ) * (2 + y)) := by
    rw [Real.log_mul hq0.ne' (by positivity)]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith : 2 ≤ 2 + y)
    linarith [log_two_ge_two_thirds]
  have ha : Real.log q / 2 + 9 / 10 ≤
      0.5 * Real.log ((q : ℝ) * (2 + y)) + 0.59773 := by linarith
  have ha0 : 0 ≤ 0.5 * Real.log ((q : ℝ) * (2 + y)) + 0.59773 := by linarith
  have hc : 12 ≤ 7 * (1 + 3 / Real.pi) := by
    have h : (3 / 4 : ℝ) ≤ 3 / Real.pi := by
      apply (le_div_iff₀ hpi0).mpr
      linarith
    linarith
  have hbulk : 6 * Real.log q + 54 / 5 ≤
      7 * (1 + 3 / Real.pi) * (0.5 * Real.log ((q : ℝ) * (2 + y)) + 0.59773) := by
    have h := mul_le_mul_of_nonneg_right hc ha0
    linarith
  have hatan : 0 ≤ 1 / (2 * Real.pi) * Real.arctan (2 * y / 3) := by
    apply mul_nonneg (by positivity)
    exact Real.arctan_nonneg.mpr (by positivity)
  have hrec : 0 ≤ 1 / (4 * ‖(1 / 2 : ℂ) + (y : ℂ) * Complex.I‖) := by positivity
  have hlast : 0 ≤ 4 / Real.pi * (0.6105 +
      1.5 / (‖(0.5 : ℂ) + (y : ℂ) * Complex.I‖ *
        ‖(2 : ℂ) + (y : ℂ) * Complex.I‖) + 1.5 / 4) := by positivity
  unfold sourceSixBound
  linarith

theorem count_le_sourceSix_low {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    {chi : Character q} (hchi : chi ≠ 1) (alpha : ℝ)
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (count chi alpha y : ℝ) ≤ sourceSixBound q y := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : (2 / 3 : ℝ) ≤ Real.log q := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq3
    norm_num at h
    linarith
  have hlog : Real.log (y + 3) ≤ 2 := by
    have h := Real.log_le_log (by linarith : 0 < y + 3)
      (by linarith : y + 3 ≤ 4)
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at h
    norm_num at h
    linarith
  have hm : nonprincipalBound q y ≤ 5 * (Real.log q / 2 + 9 / 4) := by
    unfold nonprincipalBound
    apply mul_le_mul (by linarith) (by linarith) _ (by norm_num)
    have h := Real.log_nonneg (by linarith : 1 ≤ y + 3)
    linarith
  exact (count_le_modulus hchi alpha hy).trans
    (hm.trans ((by linarith : 5 * (Real.log q / 2 + 9 / 4) ≤
      6 * Real.log q + 54 / 5).trans (sourceSixBound_low_lower hq hy hy1)))

end LiuWang.Proof.DirichletZeroCount
