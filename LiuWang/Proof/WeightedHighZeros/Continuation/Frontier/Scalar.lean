import LiuWang.Proof.WeightedHighZeros.Continuation.SourceIntegral

/-! # Uniform scalar payment for the `49/50` frontier -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.WeightedHighZeros.Continuation.Frontier

theorem baseline_payment :
    2000000 * 81 * (3100 : ℝ) ^ (4 : ℕ) * Real.exp (-62) ≤ 1 / 10000 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8 / 3)
    (show (8 / 3 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 62
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat, mul_one] at h
  have hb : 10000 * 2000000 * 81 * (3100 : ℝ) ^ (4 : ℕ) ≤ Real.exp 62 :=
    le_trans (by norm_num) h
  rw [Real.exp_neg]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mpr
  have hh := (div_le_one (Real.exp_pos 62)).mpr hb
  convert hh using 1
  ring

theorem scaled_decay_le {L : ℝ} (hL : 3100 ≤ L) :
    (L / 3100) ^ (6 : ℕ) * Real.exp (-L / 50) ≤ Real.exp (-62) := by
  have hx : 0 < L / 3100 := by positivity
  have hl := Real.log_le_sub_one_of_pos hx
  have he : 6 * Real.log (L / 3100) - L / 50 ≤ -62 := by linarith
  calc
    _ = Real.exp (6 * Real.log (L / 3100) - L / 50) := by
      rw [show (L / 3100) ^ (6 : ℕ) = Real.exp (6 * Real.log (L / 3100)) by
        rw [show 6 * Real.log (L / 3100) =
          Real.log ((L / 3100) ^ (6 : ℕ)) by
            simp only [Real.log_pow, Nat.cast_ofNat], Real.exp_log (by positivity)]]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem frontier_scalar_payment {L : ℝ} (hL : 3100 ≤ L) :
    2000000 * Real.log L ^ (2 : ℕ) * Real.exp (-L / 50) ≤
      (1 / 10000 : ℝ) / L ^ (4 : ℕ) := by
  have hL0 : 0 < L := by linarith
  have hlog : Real.log L ≤ 9 * (L / 3100) := by
    linarith [log_le_original_linear hL]
  have hsq := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ L)) hlog 2
  apply (le_div_iff₀ (pow_pos hL0 4)).mpr
  calc
    _ ≤ (2000000 * (9 * (L / 3100)) ^ (2 : ℕ) * Real.exp (-L / 50)) *
        L ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)) (by positivity)
    _ = (2000000 * 81 * (3100 : ℝ) ^ (4 : ℕ)) *
        ((L / 3100) ^ (6 : ℕ) * Real.exp (-L / 50)) := by ring
    _ ≤ (2000000 * 81 * (3100 : ℝ) ^ (4 : ℕ)) * Real.exp (-62) :=
      mul_le_mul_of_nonneg_left (scaled_decay_le hL) (by norm_num)
    _ ≤ _ := baseline_payment

theorem remaining_coefficient : (0.0126 : ℝ) - 1 / 10000 = 1 / 80 := by norm_num

end LiuWang.Proof.WeightedHighZeros.Continuation.Frontier
