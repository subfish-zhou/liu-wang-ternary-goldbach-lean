import LiuWang.Proof.Campaign20260915.LowZeroMoment.AllZerosFourteen
import LiuWang.Proof.Campaign20260915.Totient.RSZeroDifferenceSum

set_option autoImplicit false
noncomputable section

open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.LowZeroMoment
open LiuWang.Proof.Campaign20260915.Totient

theorem rsZeroMoment_le_third_div_fourteen {m : ℕ} (hm : 3 ≤ m)
    (L : ℝ) (p : RiemannXiDivisorZeroIndex) :
    rsZeroMoment m L p ≤ rsZeroMoment 3 L p / (14 : ℝ) ^ (m - 3) := by
  have ht := xi_zero_height_gt_fourteen p
  have ht0 : 0 < |(riemannXiDivisorZeroValue p).im| := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 14) ht.le (m - 3)
  have hm' : m + 1 = 4 + (m - 3) := by omega
  unfold rsZeroMoment
  rw [hm', pow_add, div_div]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
    (mul_le_mul_of_nonneg_left hp (by positivity))

theorem rsZeroMoment_sum_le_third_div_fourteen {m : ℕ} (hm : 3 ≤ m)
    {L : ℝ} (hL : 0 ≤ L) :
    (∑' p, rsZeroMoment m L p) ≤
      (∑' p, rsZeroMoment 3 L p) / (14 : ℝ) ^ (m - 3) := by
  have h := (rsZeroMoment_summable (by omega : 1 ≤ m) hL).tsum_le_tsum
    (rsZeroMoment_le_third_div_fourteen hm L)
    ((rsZeroMoment_summable (by norm_num : 1 ≤ 3) hL).div_const ((14 : ℝ) ^ (m - 3)))
  simpa only [tsum_div_const] using h

theorem fourteen_rpow_three_sub {m : ℕ} (hm : 3 ≤ m) :
    (14 : ℝ) ^ (3 - (m : ℝ)) = 1 / (14 : ℝ) ^ (m - 3) := by
  have he : 3 - (m : ℝ) = -((m - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm]
    push_cast
    ring
  rw [he, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

theorem xi_height_moment_le_third {m : ℕ} (hm : 3 ≤ m) :
    (∑' p : RiemannXiDivisorZeroIndex,
      1 / |(riemannXiDivisorZeroValue p).im| ^ (m + 1)) ≤
      (14 : ℝ) ^ (3 - (m : ℝ)) *
        ∑' p : RiemannXiDivisorZeroIndex,
          1 / |(riemannXiDivisorZeroValue p).im| ^ 4 := by
  have h := rsZeroMoment_sum_le_third_div_fourteen hm (L := 0) (by norm_num)
  simp only [rsZeroMoment, mul_zero, Real.exp_zero, Nat.reduceAdd] at h
  rw [fourteen_rpow_three_sub hm]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

#print axioms rsZeroMoment_le_third_div_fourteen
#print axioms rsZeroMoment_sum_le_third_div_fourteen
#print axioms xi_height_moment_le_third

end LiuWang.Proof.Campaign20260915.LowZeroMoment
