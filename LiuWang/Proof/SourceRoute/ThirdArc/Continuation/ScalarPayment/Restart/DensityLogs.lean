import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.StripScalar
import LiuWang.Proof.WeightedLowZeros.Continuation.LogBudget

/-! Original enlarged height and coupled logarithmic domains for (5.24). -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem lowHeight_log_bounds : 10 ≤ Real.log lowHeight ∧ Real.log lowHeight ≤ 10.36 := by
  have hlo := pow_le_pow_left₀ (Real.exp_pos 1).le
    (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 10
  have hhi := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.718)
    (by linarith [Real.exp_one_gt_d9] : (2.718 : ℝ) ≤ Real.exp 1) 10
  rw [← Real.exp_nat_mul] at hlo hhi
  norm_num only [Nat.cast_ofNat, mul_one] at hlo hhi
  constructor
  · apply (Real.le_log_iff_exp_le lowHeight_pos).mpr
    unfold lowHeight
    nlinarith [Real.pi_gt_three]
  · apply (Real.log_le_iff_le_exp lowHeight_pos).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.36) 4
    norm_num [Finset.sum_range_succ] at he
    have hp := mul_le_mul hhi he (by norm_num) (Real.exp_pos _).le
    rw [← Real.exp_add] at hp
    norm_num only [show (10 : ℝ) + 0.36 = 10.36 by norm_num] at hp
    unfold lowHeight
    nlinarith [Real.pi_lt_d2]

theorem log_ten_le : Real.log 10 ≤ 2.31 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).mpr
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.718)
    (by linarith [Real.exp_one_gt_d9] : (2.718 : ℝ) ≤ Real.exp 1) 2
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat, mul_one] at h
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.31) 4
  norm_num [Finset.sum_range_succ] at he
  have hp := mul_le_mul h he (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at hp
  norm_num at hp ⊢
  linarith

theorem enlarged_height_logs {t : ℝ} (ht : 24 ≤ t) :
    36 ≤ t + Real.log (10000 * t) ∧
      t + Real.log (10000 * t) ≤ (11 / 10) * (t + Real.log lowHeight) := by
  have ht0 : 0 < t := by linarith
  have h10 : 0 < (10 : ℝ) := by norm_num
  have h10000 : Real.log (10000 : ℝ) = 4 * Real.log 10 := by
    rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlower : 9 ≤ Real.log (10000 : ℝ) := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10000)).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 9
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  have htl : 3 ≤ Real.log t := by
    apply (Real.le_log_iff_exp_le ht0).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 3
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  have htu := Real.log_le_sub_one_of_pos (div_pos ht0 h10)
  rw [Real.log_div ht0.ne' h10.ne'] at htu
  rw [Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0) ht0.ne']
  constructor
  · linarith
  · rw [h10000]
    linarith [log_ten_le, lowHeight_log_bounds.1]

theorem M3_density_logs {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    24 ≤ Real.log q ∧
      36 ≤ Real.log ((q : ℝ) * (10000 * Real.log q)) ∧
      Real.log ((q : ℝ) * (10000 * Real.log q)) ≤
        (11 / 10) * Real.log ((q : ℝ) * lowHeight) ∧
      4 * Real.log ((q : ℝ) * (10000 * Real.log q)) ≤ sourceL N / 10 := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hqR : (0 : ℝ) < q := lt_of_lt_of_le (pow_pos hL0 3) hq
  have hlogL : 8 ≤ Real.log (sourceL N) :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have htlo := Real.log_le_log (pow_pos hL0 3) hq
  have hthi := Real.log_le_log hqR hq1
  change Real.log (sourceL N ^ 3) ≤ Real.log q at htlo
  change Real.log q ≤ Real.log (sourceL N ^ 6) at hthi
  rw [Real.log_pow] at htlo hthi
  norm_num only [Nat.cast_ofNat] at htlo hthi
  have ht : 24 ≤ Real.log q := by linarith
  have hs := enlarged_height_logs ht
  have hz : Real.log ((q : ℝ) * (10000 * Real.log q)) =
      Real.log q + Real.log (10000 * Real.log q) :=
    Real.log_mul hqR.ne' (by positivity)
  have hh := Real.log_mul hqR.ne' lowHeight_pos.ne'
  have hratio := log_over_self_bound hL
  have hlb : Real.log (sourceL N) ≤ (8.04 / 3100) * sourceL N :=
    (div_le_iff₀ hL0).mp hratio
  refine ⟨ht, by simpa only [hz] using hs.1,
    by simpa only [hz, hh] using hs.2, ?_⟩
  rw [hz]
  nlinarith [hs.2, lowHeight_log_bounds.2]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
