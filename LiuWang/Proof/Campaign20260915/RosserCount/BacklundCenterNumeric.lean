import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiniteLower

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Complex Finset

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundRootUpper32 : ℕ → ℚ
  | 1 => 1000 / 1000
  | 2 => 1415 / 1000
  | 3 => 1733 / 1000
  | 4 => 2000 / 1000
  | 5 => 2237 / 1000
  | 6 => 2450 / 1000
  | 7 => 2646 / 1000
  | 8 => 2829 / 1000
  | 9 => 3000 / 1000
  | 10 => 3163 / 1000
  | 11 => 3317 / 1000
  | 12 => 3465 / 1000
  | 13 => 3606 / 1000
  | 14 => 3742 / 1000
  | 15 => 3873 / 1000
  | 16 => 4000 / 1000
  | 17 => 4124 / 1000
  | 18 => 4243 / 1000
  | 19 => 4359 / 1000
  | 20 => 4473 / 1000
  | 21 => 4583 / 1000
  | 22 => 4691 / 1000
  | 23 => 4796 / 1000
  | 24 => 4899 / 1000
  | 25 => 5000 / 1000
  | 26 => 5100 / 1000
  | 27 => 5197 / 1000
  | 28 => 5292 / 1000
  | 29 => 5386 / 1000
  | 30 => 5478 / 1000
  | 31 => 5568 / 1000
  | 32 => 5657 / 1000
  | _ => 1

theorem backlund_root_upper_certificates {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 32) :
    0 < (backlundRootUpper32 n : ℝ) ∧ (n : ℝ) ≤ (backlundRootUpper32 n : ℝ) ^ 2 := by
  interval_cases n <;> norm_num [backlundRootUpper32]

theorem backlund_zeta_five_halves_lower : (4 / 3 : ℝ) ≤ ‖riemannZeta (5 / 2 : ℂ)‖ := by
  have h := backlund_finite_dirichlet_lower (σ := 5 / 2) (by norm_num) 32
  have hsum : (∑ n ∈ range 32, 1 / ((n + 1 : ℝ) ^ 2 * (backlundRootUpper32 (n + 1) : ℝ))) ≤
      ∑ n ∈ range 32, (n + 1 : ℝ) ^ (-5 / 2 : ℝ) := by
    apply sum_le_sum
    intro n hn
    have hn32 := mem_range.mp hn
    have hu := backlund_root_upper_certificates (n := n + 1) (by omega) (by omega)
    apply backlund_five_halves_term_lower (by positivity) hu.1
    simpa only [Nat.cast_add, Nat.cast_one] using hu.2
  have hfinite : (4 / 3 : ℝ) ≤
      ∑ n ∈ range 32, 1 / ((n + 1 : ℝ) ^ 2 * (backlundRootUpper32 (n + 1) : ℝ)) := by
    norm_num [Finset.sum_range_succ, backlundRootUpper32]
  exact (hfinite.trans hsum).trans (by simpa [neg_div] using h)

theorem backlund_log_five_halves_lower :
    (287 / 1000 : ℝ) ≤ Real.log ‖riemannZeta (5 / 2 : ℂ)‖ := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 7)
    (by norm_num : (1 / 7 : ℝ) < 1) 4
  rw [show (1 + (1 / 7 : ℝ)) / (1 - 1 / 7) = 4 / 3 by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4 / 3) backlund_zeta_five_halves_lower
  linarith

theorem backlund_center_log_numeric (T : ℝ) :
    -(6207 / 5000 : ℝ) ≤ Real.log ‖riemannZeta (backlundCenterPoint T)‖ := by
  have h := backlund_center_log_lower T
  linarith [backlund_log_five_halves_lower, backlund_real_center_log_upper]

#print axioms backlund_root_upper_certificates
#print axioms backlund_zeta_five_halves_lower
#print axioms backlund_log_five_halves_lower
#print axioms backlund_center_log_numeric

end LiuWang.Proof.Campaign20260915.RosserCount
