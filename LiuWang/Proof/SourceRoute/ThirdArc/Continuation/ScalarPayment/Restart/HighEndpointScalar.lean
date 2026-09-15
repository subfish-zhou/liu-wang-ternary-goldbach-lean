import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityLogs

/-! Exact all-L certification of the original (5.41) endpoint density price. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

def highEndpointDensity (L : ℝ) : ℝ :=
  (33643 + 254231 / (21 * Real.log L)) * (21 * Real.log L) ^ 6 * L ^ (78 / 60 : ℝ)

theorem high_endpoint_rpow_certificate : (3100 : ℝ) ^ (78 / 60 : ℝ) ≤ 34720 := by
  have he : ((3100 : ℝ) ^ (78 / 60 : ℝ)) ^ (10 : ℕ) = (3100 : ℝ) ^ (13 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3100)]
    norm_num
  apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (10 : ℕ) ≠ 0)).mp
  rw [he]
  norm_num

theorem high_endpoint_rpow_global {L : ℝ} (hL : 3100 ≤ L) :
    L ^ (78 / 60 : ℝ) ≤ 34720 * (L / 3100) ^ 2 := by
  have hr : (1 : ℝ) ≤ L / 3100 := by linarith
  have h := Real.rpow_le_rpow_of_exponent_le hr
    (by norm_num : (78 / 60 : ℝ) ≤ (2 : ℕ))
  rw [Real.rpow_natCast] at h
  calc
    _ = ((3100 : ℝ) * (L / 3100)) ^ (78 / 60 : ℝ) := by congr 1; ring
    _ = (3100 : ℝ) ^ (78 / 60 : ℝ) * (L / 3100) ^ (78 / 60 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := mul_le_mul high_endpoint_rpow_certificate h (by positivity) (by norm_num)

theorem high_endpoint_density_global {L : ℝ} (hL : 3100 ≤ L) :
    highEndpointDensity L ≤
      (33643 + 254231 / 168) * (21 * 8.04) ^ 6 * 34720 * (L / 3100) ^ 8 := by
  have hL0 : 0 < L := by linarith
  have hl : 8 ≤ Real.log L := log_3100_bounds.1.trans
    (Real.log_le_log (by norm_num) hL)
  have hu := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
  have hu : Real.log L ≤ 8.04 * (L / 3100) := by nlinarith
  have hc : 33643 + 254231 / (21 * Real.log L) ≤ 33643 + 254231 / 168 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 254231)
      (by norm_num : (0 : ℝ) < 168) (show 168 ≤ 21 * Real.log L by linarith)
    linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 21 * Real.log L by linarith)
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 21)) 6
  have h := mul_le_mul
    (mul_le_mul hc hp (pow_nonneg (by linarith) 6) (by norm_num))
    (high_endpoint_rpow_global hL) (by positivity) (by positivity)
  unfold highEndpointDensity
  ring_nf at h ⊢
  exact h

theorem high_endpoint_price_certificate :
    (5 * 0.11585 * (33643 + 254231 / 168) * (21 * 8.04) ^ 6 * 34720 : ℝ) ≤
      (7 / 10 ^ (31 : ℕ)) * 3100 ^ 15 := by norm_num

theorem high_endpoint_scalar_paid {L : ℝ} (hL : 3100 ≤ L) :
    5 * 0.11585 * highEndpointDensity L / L ^ 15 ≤ 7 / 10 ^ (31 : ℕ) := by
  have hL0 : 0 < L := by linarith
  have hr : (1 : ℝ) ≤ L / 3100 := by linarith
  have hp := pow_le_pow_right₀ hr (by norm_num : (8 : ℕ) ≤ 15)
  have h := mul_le_mul_of_nonneg_left (high_endpoint_density_global hL)
    (by norm_num : (0 : ℝ) ≤ 5 * 0.11585)
  have hp := mul_le_mul_of_nonneg_left hp
    (by norm_num : (0 : ℝ) ≤
      5 * 0.11585 * (33643 + 254231 / 168) * (21 * 8.04) ^ 6 * 34720)
  have hc := mul_le_mul_of_nonneg_right high_endpoint_price_certificate
    (pow_nonneg (show 0 ≤ L / 3100 by linarith) 15)
  apply (div_le_iff₀ (pow_pos hL0 15)).mpr
  nlinarith only [h, hp, hc]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
