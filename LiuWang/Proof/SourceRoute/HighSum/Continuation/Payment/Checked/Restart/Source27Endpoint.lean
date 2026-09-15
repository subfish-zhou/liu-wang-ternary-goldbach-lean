import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.Source27Analysis

/-! # Small exact Taylor certificates for the (2.27) endpoint, not quadrature -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

theorem source27_log_3100 : Real.log (3100 : ℝ) ≤ 8.03916 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 8
  rw [← Real.exp_nat_mul] at h1
  norm_num only [Nat.cast_ofNat, mul_one] at h1
  have h2 := Real.sum_le_exp_of_nonneg (x := (0.03916 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h2
  have h := mul_le_mul h1 h2 (by norm_num) (Real.exp_pos 8).le
  rw [← Real.exp_add] at h
  norm_num at h
  linarith

theorem source27_log_endpoint :
    Real.log (10000 * (3100 : ℝ) ^ (3 : ℕ) * Real.log ((3100 : ℝ) ^ (3 : ℕ))) ≤
      36.511 := by
  have hx : 0 < 10000 * (3100 : ℝ) ^ (3 : ℕ) * Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    have h := log_3100_bounds.1
    rw [Real.log_pow]
    positivity
  apply (Real.log_le_iff_le_exp hx).mpr
  have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 36
  rw [← Real.exp_nat_mul] at h1
  norm_num only [Nat.cast_ofNat, mul_one] at h1
  have h2 := Real.sum_le_exp_of_nonneg (x := (0.511 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at h2
  have h := mul_le_mul h1 h2 (by norm_num) (Real.exp_pos 36).le
  rw [← Real.exp_add] at h
  norm_num at h
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [source27_log_3100]

theorem source27_endpoint_certificate :
    (3100 : ℝ) ^ (4 : ℕ) * source27Primitive (0.478 * 3100) 0.87399 36.511 ≤ 0.00197 := by
  let k : ℝ := 0.478 * 3100
  let b : ℝ := 36.511
  let P : ℝ :=
    (b ^ (3 : ℕ) / Real.pi - 0.87399 * b ^ (2 : ℕ)) / k -
      (3 * b ^ (4 : ℕ) / Real.pi - 2 * 0.87399 * b ^ (3 : ℕ)) / k ^ (2 : ℕ) +
      (12 * b ^ (5 : ℕ) / Real.pi - 6 * 0.87399 * b ^ (4 : ℕ)) / k ^ (3 : ℕ)
  have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 40
  rw [← Real.exp_nat_mul] at h1
  norm_num only [Nat.cast_ofNat, mul_one] at h1
  have h2 := Real.sum_le_exp_of_nonneg (x := k / b - 40) (by norm_num [k, b]) 10
  norm_num [Finset.sum_range_succ, k, b] at h2
  have h := mul_le_mul h1 h2 (by norm_num) (Real.exp_pos 40).le
  rw [← Real.exp_add] at h
  norm_num at h
  have hP : P ≤
      (b ^ (3 : ℕ) / k - 3 * b ^ (4 : ℕ) / k ^ (2 : ℕ) +
        12 * b ^ (5 : ℕ) / k ^ (3 : ℕ)) / 3.141592 -
      0.87399 * (b ^ (2 : ℕ) / k - 2 * b ^ (3 : ℕ) / k ^ (2 : ℕ) +
        6 * b ^ (4 : ℕ) / k ^ (3 : ℕ)) := by
    have hpi := div_le_div_of_nonneg_left
      (show 0 ≤ b ^ (3 : ℕ) / k - 3 * b ^ (4 : ℕ) / k ^ (2 : ℕ) +
        12 * b ^ (5 : ℕ) / k ^ (3 : ℕ) by norm_num [b, k])
      (by norm_num : (0 : ℝ) < 3.141592) Real.pi_gt_d6.le
    dsimp only [P]
    convert! sub_le_sub_right hpi
      (0.87399 * (b ^ (2 : ℕ) / k - 2 * b ^ (3 : ℕ) / k ^ (2 : ℕ) +
        6 * b ^ (4 : ℕ) / k ^ (3 : ℕ))) using 1
    ring
  have hpay : (3100 : ℝ) ^ (4 : ℕ) * P ≤ 0.00197 * Real.exp (k / b) := by
    norm_num [k, b] at hP ⊢
    linarith
  change (3100 : ℝ) ^ (4 : ℕ) * (P * Real.exp (-k / b)) ≤ _
  rw [show -k / b = -(k / b) by ring, Real.exp_neg]
  rw [← mul_assoc, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr hpay

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
