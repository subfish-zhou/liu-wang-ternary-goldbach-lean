import LiuWang.Proof.DirichletZeroCount.Remainder.SourceSix

/-! # The literal principal companion Theorem 5, paid from the stronger xi count -/

set_option autoImplicit false
noncomputable section
open Complex
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def sourceFiveBound (y : ℝ) : ℝ :=
  y / Real.pi * Real.log (Real.sqrt ((5 / 4 : ℝ) ^ 2 + (y / 2) ^ 2)) +
    3 / (2 * Real.pi) * Real.arctan (2 * y / 5) -
    (1 + Real.log Real.pi) / Real.pi * y +
    0.5114 * 2 + 1 / (2 * Real.sqrt (25 + 4 * y ^ 2)) +
    10.5 * (2.25 + Real.pi) / Real.pi *
      (0.5 * Real.log (2 + y) + 0.25 / (0.0625 + y ^ 2) + 2.6459) +
    3 / Real.pi * (0.6105 + 1 / ‖(1 : ℂ) + (y : ℂ) * I‖ + 1 / y + 1.5 / 4)

theorem sourceFive_norm_identity (y : ℝ) :
    Real.sqrt ((5 / 4 : ℝ) ^ 2 + (y / 2) ^ 2) =
      ‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖ / 2 := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (norm_nonneg _) (by norm_num))).mp
  rw [Real.sq_sqrt (by positivity)]
  simp only [div_pow]
  rw [← normSq_eq_norm_sq]
  norm_num [normSq_apply]
  ring

theorem sourceFiveBound_lower {y : ℝ} (hy : 0 < y) :
    (sourceGammaMain (5 / 2) y - y * Real.log Real.pi + 1.0228 * Real.pi +
      10.5 * (2.25 + Real.pi) * (Real.log (2 + y) / 2 + 2.6459) + 2.9565) / Real.pi ≤
        sourceFiveBound y := by
  have hr : 0 ≤ 1 / (2 * Real.sqrt (25 + 4 * y ^ 2)) := by positivity
  have hg : 0 ≤ 10.5 * (2.25 + Real.pi) / Real.pi * (0.25 / (0.0625 + y ^ 2)) := by positivity
  have hp : 0 ≤ 3 / Real.pi * (1 / ‖(1 : ℂ) + (y : ℂ) * I‖ + 1 / y) := by positivity
  have he : sourceFiveBound y =
      (sourceGammaMain (5 / 2) y - y * Real.log Real.pi + 1.0228 * Real.pi +
        10.5 * (2.25 + Real.pi) * (Real.log (2 + y) / 2 + 2.6459) + 2.9565) / Real.pi +
          1 / (2 * Real.sqrt (25 + 4 * y ^ 2)) +
          10.5 * (2.25 + Real.pi) / Real.pi * (0.25 / (0.0625 + y ^ 2)) +
          3 / Real.pi * (1 / ‖(1 : ℂ) + (y : ℂ) * I‖ + 1 / y) := by
    unfold sourceFiveBound sourceGammaMain
    rw [sourceFive_norm_identity, show y / (5 / 2 : ℝ) = 2 * y / 5 by ring]
    field_simp [Real.pi_ne_zero]
    ring
  rw [he]
  linarith

theorem sourceGammaMain_four_le_fiveHalves {y : ℝ} (hy : 0 ≤ y) :
    sourceGammaMain 4 y ≤ sourceGammaMain (5 / 2) y + 3 / 2 + 3 * Real.pi / 2 := by
  let r := ‖((5 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖
  let s := ‖((4 : ℝ) : ℂ) + (y : ℂ) * I‖
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) (re_le_norm _)
  have hs : 0 < s := lt_of_lt_of_le (by norm_num) (re_le_norm _)
  have hyr : y ≤ r := by simpa [r] using im_le_norm (((5 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
  have hsr : s ≤ r + 3 / 2 := by
    have he : ((4 : ℝ) : ℂ) + (y : ℂ) * I =
        (((5 / 2 : ℝ) : ℂ) + (y : ℂ) * I) + ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
    dsimp only [s, r]
    rw [he]
    convert! norm_add_le (((5 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ((3 / 2 : ℝ) : ℂ) using 1
    norm_num
  have hlog : Real.log (s / r) ≤ (3 / 2) / r :=
    (Real.log_le_sub_one_of_pos (div_pos hs hr)).trans
      ((le_div_iff₀ hr).mpr (by rw [sub_mul, div_mul_cancel₀ _ hr.ne']; linarith))
  have hlogdiff : Real.log (s / 2) - Real.log (r / 2) = Real.log (s / r) := by
    rw [Real.log_div hs.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hr.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_div hs.ne' hr.ne']
    ring
  have hphase : y * (Real.log (s / 2) - Real.log (r / 2)) ≤ 3 / 2 := by
    rw [hlogdiff]
    apply (mul_le_mul_of_nonneg_left hlog hy).trans
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hr).mpr (by linarith)
  have hlow := Real.arctan_nonneg.mpr (div_nonneg hy (by norm_num : (0 : ℝ) ≤ 5 / 2))
  have hhigh := Real.arctan_lt_pi_div_two (y / 4)
  change y * Real.log (s / 2) - y + (4 - 1) * Real.arctan (y / 4) ≤
    y * Real.log (r / 2) - y + (5 / 2 - 1) * Real.arctan (y / (5 / 2)) + 3 / 2 + 3 * Real.pi / 2
  nlinarith

theorem uniformXiCountBound_le_sourceFive {y : ℝ} (hy : 0 < y) :
    uniformXiCountBound y ≤ sourceFiveBound y := by
  have hl : 0 ≤ Real.log (2 + y) := Real.log_nonneg (by linarith)
  have hg := sourceGammaMain_four_le_fiveHalves hy.le
  apply le_trans _ (sourceFiveBound_lower hy)
  unfold uniformXiCountBound uniformXiFee
  rw [abs_of_pos hy, add_comm y 2]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have hp := mul_nonneg Real.pi_pos.le hl
  nlinarith [Real.pi_gt_three]

theorem count_principal_le_sourceFive (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 < y) :
    (count (1 : Character q) alpha y : ℝ) ≤ sourceFiveBound y :=
  (principal_count_alpha_le_uniform q ha hy.le).trans (uniformXiCountBound_le_sourceFive hy)

theorem source_principal_zero_height (q : ℕ) [NeZero q] (alpha : ℝ) :
    count (1 : Character q) alpha 0 = 0 := count_principal_zero_height q alpha

end LiuWang.Proof.DirichletZeroCount.Remainder
