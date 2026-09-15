import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.LocalTaylor
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.EulerBound
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Scale

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

theorem original_height_precise : Real.log lowHeight ≤ (10.3550703 : ℝ) := by
  apply (Real.log_le_iff_le_exp (by unfold lowHeight; positivity)).mpr
  have h := exp_nat_add_lower 10 11 (u := 0.3550703) (b := 31415.9265359)
    (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h
  unfold lowHeight
  linarith [Real.pi_lt_d20]

theorem endpoint_logs :
    heightLog (6 * Real.log 3100) ≤ (13.08642418 : ℝ) ∧
      densityLog (6 * Real.log 3100) ≤ (61.3213686 : ℝ) := by
  have h := exp_nat_add_lower 9 10 (u := 0.21034038) (b := 10000)
    (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h
  have hl : Real.log (10000 : ℝ) ≤ 9.21034038 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr (by norm_num; exact h)
  have hs := log_3100_precise
  have hu : heightLog (6 * Real.log 3100) ≤ (13.08642418 : ℝ) := by
    unfold heightLog
    rw [Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0) (by linarith [hs.1] :
      6 * Real.log (3100 : ℝ) ≠ 0)]
    linarith [log_48_precise.2]
  exact ⟨hu, by unfold densityLog; linarith [hs.2]⟩

theorem endpoint_power : (6 * Real.log 3100) ^ (1 / 15 : ℝ) ≤ (1.294864 : ℝ) := by
  have hs0 : 0 < 6 * Real.log (3100 : ℝ) := by linarith [log_3100_precise.1]
  rw [Real.rpow_def_of_pos hs0]
  have h := exp_nat_add_upper 0 10 (u := 0.25840559) (b := 1.294864)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h
  norm_num
  exact (Real.exp_le_exp.mpr (show Real.log (6 * Real.log 3100) * (1 / 15 : ℝ) ≤
    25840559 / 100000000 by linarith [log_48_precise.2])).trans h

theorem endpoint_nu :
    logNu (6 * Real.log 3100) ≤ 1.781074 * 3.8760838 + 2.50637 / 3.8760837 := by
  have h := mul_le_mul exp_euler_upper log_48_precise.2
    (by linarith [log_48_precise.1]) (by norm_num)
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2.50637)
    (by norm_num : (0 : ℝ) < 3.8760837) log_48_precise.1
  exact add_le_add h hd

theorem endpoint_exponent :
    -(9 / 20 : ℝ) * (6 * Real.log 3100) -
      0.478 * 3100 / (6 * Real.log 3100 + Real.log lowHeight) ≤ -46.9967238 := by
  have hs := log_3100_precise
  have ht : 0 < 6 * Real.log (3100 : ℝ) + Real.log lowHeight := by
    linarith [hs.1, lowHeight_log_bounds.1]
  have hu : 6 * Real.log (3100 : ℝ) + Real.log lowHeight ≤ 58.5900147 := by
    linarith [hs.2, original_height_precise]
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 0.478 * 3100) ht hu
  norm_num at hd
  linarith [hs.1]

theorem endpoint_rational_certificate :
    (3100 * 1.8771 * (1.781074 * 3.8760838 + 2.50637 / 3.8760837) * 1.294864 *
      (254231 * (61.3213686 : ℝ) ^ 5 + 17102 * (61.3213686 : ℝ) ^ 6)) *
      Real.exp (-46.9967238) ≤ (0.249809 : ℝ) := by
  have h := exp_nat_add_lower 46 16 (u := 0.9967238) (by norm_num) (le_refl _)
  norm_num only [Nat.cast_ofNat, show (46 : ℝ) + 0.9967238 = 46.9967238 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
  linarith only [h]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
