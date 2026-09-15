import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.MovingDomains

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

theorem log_3100_ge_eight : (8 : ℝ) ≤ Real.log 3100 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3100)).mpr
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 8
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

theorem original_scalar_density_domain_failure :
    10 * Real.pi * (3100 : ℝ) ^ 7 / (3100 : ℝ) ^ 6 <
      10000 * Real.log ((3100 : ℝ) ^ 6) := by
  rw [Real.log_pow]
  norm_num
  linarith [Real.pi_lt_four, log_3100_ge_eight]

theorem sourceL_ceil_exp_3100 :
    3100 ≤ sourceL ⌈Real.exp 3100⌉₊ ∧ sourceL ⌈Real.exp 3100⌉₊ < 3101 := by
  have hN : Real.exp 3100 ≤ (⌈Real.exp 3100⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨sourceL_ge_3100 hN, ?_⟩
  have hn0 := natCast_pos_of_exp_le hN
  change Real.log (⌈Real.exp 3100⌉₊ : ℝ) < 3101
  apply (Real.log_lt_iff_lt_exp hn0).mpr
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos 3100).le
  have he : 1 ≤ Real.exp 3100 := Real.one_le_exp_iff.mpr (by norm_num)
  have htwo : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hprod := mul_lt_mul_of_pos_left htwo (Real.exp_pos 3100)
  rw [← Real.exp_add] at hprod
  norm_num only [show (3100 : ℝ) + 1 = 3101 by norm_num] at hprod
  linarith

theorem original_integer_density_domain_failure :
    ∃ N q : ℕ, Real.exp 3100 ≤ (N : ℝ) ∧
      sourceP N < (q : ℝ) ∧ (q : ℝ) ≤ sourceP1 N ∧
      middleHeight N q < 10000 * Real.log q := by
  refine ⟨⌈Real.exp 3100⌉₊, 3100 ^ 6, Nat.le_ceil _, ?_, ?_, ?_⟩
  · have h := pow_le_pow_left₀ (by linarith [sourceL_ceil_exp_3100.1] :
        0 ≤ sourceL ⌈Real.exp 3100⌉₊) sourceL_ceil_exp_3100.2.le 3
    change sourceL ⌈Real.exp 3100⌉₊ ^ 3 < ((3100 ^ 6 : ℕ) : ℝ)
    norm_num at h ⊢
    linarith
  · have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100)
      sourceL_ceil_exp_3100.1 6
    simpa only [sourceP1, Nat.cast_pow, Nat.cast_ofNat] using h
  · have hL0 : 0 ≤ sourceL ⌈Real.exp 3100⌉₊ := by linarith [sourceL_ceil_exp_3100.1]
    have hpow := pow_le_pow_left₀ hL0 sourceL_ceil_exp_3100.2.le 7
    have hpi := mul_le_mul_of_nonneg_left Real.pi_lt_four.le
      (show 0 ≤ 10 * sourceL ⌈Real.exp 3100⌉₊ ^ 7 by positivity)
    have hlog : 48 ≤ Real.log (((3100 ^ 6 : ℕ) : ℝ)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      norm_num
      linarith [log_3100_ge_eight]
    unfold middleHeight
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < ((3100 ^ 6 : ℕ) : ℝ))).mpr
    norm_num at hpow hpi hlog ⊢
    nlinarith

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
