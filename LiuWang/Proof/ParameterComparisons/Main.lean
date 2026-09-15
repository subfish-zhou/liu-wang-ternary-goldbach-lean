import LiuWang.Proof.Parameters.Main

/-! Exact final scalar budget. This does not assert the analytic major/minor
arc estimates or the combinatorial prime-power subtraction theorem. -/
set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.ParameterComparisons
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

/-- Reuse the accepted sixteenth-power bound by taking positive square roots. -/
theorem thousand_mul_cube_lt_exp_half {x : ℝ} (hx : 2000 ≤ x) :
    1000 * x ^ (3 : ℕ) < Real.exp (x / 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have he : (Real.exp (x / 2)) ^ (2 : ℕ) = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have h16 := pow_sixteen_lt_exp hx
  have h8 : x ^ (8 : ℕ) < Real.exp (x / 2) := by
    have hs : (x ^ (8 : ℕ)) ^ (2 : ℕ) < (Real.exp (x / 2)) ^ (2 : ℕ) := by
      rw [he, ← pow_mul]
      exact h16
    nlinarith [Real.exp_pos (x / 2), pow_nonneg hx0 8]
  calc
    1000 * x ^ (3 : ℕ) ≤ x * x ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hx0 _)
    _ ≤ x * x ^ (7 : ℕ) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (by norm_num)) hx0
    _ = x ^ (8 : ℕ) := by ring
    _ < Real.exp (x / 2) := h8

/-- A stronger-than-needed scalar allowance for the prime-power error. -/
theorem primePower_scalar_lt {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) <
      (3 / 1000 : ℝ) * (N : ℝ) ^ (2 : ℕ) := by
  have hp := natCast_pos_of_exp_le hN
  have h := thousand_mul_cube_lt_exp_half (sourceL_ge_2000 hN)
  have hr : (N : ℝ) ^ ((1 : ℝ) / 2) = Real.exp (sourceL N / 2) := by
    rw [Real.rpow_def_of_pos hp]
    congr 1
    unfold sourceL
    ring
  have hmul : (N : ℝ) ^ ((3 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 2) =
      (N : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_add hp]
    norm_num
  have hc : 3 * sourceL N ^ (3 : ℕ) <
      (3 / 1000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [hr]
    linarith
  have hb := mul_lt_mul_of_pos_left hc
    (Real.rpow_pos_of_pos hp ((3 : ℝ) / 2))
  calc
    3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) =
        (N : ℝ) ^ ((3 : ℝ) / 2) * (3 * sourceL N ^ (3 : ℕ)) := by ring
    _ < (N : ℝ) ^ ((3 : ℝ) / 2) *
        ((3 / 1000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2)) := hb
    _ = (3 / 1000 : ℝ) * (N : ℝ) ^ (2 : ℕ) := by
      rw [mul_left_comm, hmul]

/-- The source's final scalar comparison, retaining the available larger margin. -/
theorem final_scalar_margin {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (0.0307 : ℝ) * (N : ℝ) ^ (2 : ℕ) <
      (0.5437 - 0.51 : ℝ) * (N : ℝ) ^ (2 : ℕ) -
        3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) := by
  have h := primePower_scalar_lt (exp_2000_le_of_exp_3100_le hN)
  linarith

/-- Literal final numerical comparison; no analytic estimates are assumed here. -/
theorem final_scalar_source {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (0.03 : ℝ) * (N : ℝ) ^ (2 : ℕ) ≤
      (0.5437 - 0.51 : ℝ) * (N : ℝ) ^ (2 : ℕ) -
        3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) := by
  have h := final_scalar_margin hN
  nlinarith [sq_nonneg (N : ℝ)]
end LiuWang.Proof.ParameterComparisons
