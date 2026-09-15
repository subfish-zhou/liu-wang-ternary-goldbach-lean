import LiuWang.Proof.WeightedHighZeros.Continuation.Reciprocal

/-! # Scalar payment at the original `log N >= 3100` threshold -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.WeightedHighZeros.Continuation

theorem log_3100_le_nine : Real.log 3100 ≤ 9 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.quadratic_le_exp_of_nonneg (x := 1) (by norm_num)
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
    (show (5 / 2 : ℝ) ≤ Real.exp 1 by norm_num at h; linarith) 9
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  linarith

theorem two_million_le_exp : (2000000 : ℝ) ≤ Real.exp 22 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (show (2 : ℝ) ≤ Real.exp 1 by linarith) 22
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  linarith

theorem log_le_original_linear {L : ℝ} (hL : 3100 ≤ L) :
    Real.log L ≤ 8 + L / 3100 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < L / 3100 by positivity)
  rw [Real.log_div (by linarith : L ≠ 0) (by norm_num)] at h
  linarith [log_3100_le_nine]

theorem capped_scalar_payment {L : ℝ} (hL : 3100 ≤ L) :
    2000000 * Real.log L ^ (2 : ℕ) * Real.exp (-L / 20) ≤
      Real.exp (-75) / L ^ (4 : ℕ) := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hsq : Real.log L ^ (2 : ℕ) ≤ L ^ (2 : ℕ) :=
    pow_le_pow_left₀ hlog0 hlog 2
  have hbudget : 22 + 6 * Real.log L - L / 20 ≤ -75 := by
    have hh := log_le_original_linear hL
    linarith
  have hpay : 2000000 * L ^ (6 : ℕ) * Real.exp (-L / 20) ≤ Real.exp (-75) := by
    calc
      _ ≤ Real.exp 22 * L ^ (6 : ℕ) * Real.exp (-L / 20) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right two_million_le_exp (by positivity)) (by positivity)
      _ = Real.exp (22 + 6 * Real.log L - L / 20) := by
        rw [show L ^ (6 : ℕ) = Real.exp (6 * Real.log L) by
          rw [show 6 * Real.log L = Real.log (L ^ (6 : ℕ)) by
            simp only [Real.log_pow, Nat.cast_ofNat], Real.exp_log (by positivity)]]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hbudget
  apply (le_div_iff₀ (pow_pos hL0 4)).mpr
  calc
    _ ≤ (2000000 * L ^ (2 : ℕ) * Real.exp (-L / 20)) * L ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)) (by positivity)
    _ = 2000000 * L ^ (6 : ℕ) * Real.exp (-L / 20) := by ring
    _ ≤ _ := hpay

end LiuWang.Proof.WeightedHighZeros.Continuation
