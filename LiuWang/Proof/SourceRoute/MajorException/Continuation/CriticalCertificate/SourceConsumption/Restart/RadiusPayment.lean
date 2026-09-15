import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.LocalCost

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

theorem principalRoot_le_one : principalRoot ≤ 1 := by
  have hc : principalRoot^3 = 2.994006/Real.pi := cubeRoot_cube (by positivity)
  apply (pow_le_pow_iff_left₀ (cubeRoot_pos (by positivity)).le
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : 3 ≠ 0)).mp
  change principalRoot^3 ≤ 1^3
  rw [hc, one_pow]
  exact (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_d20])

theorem exceptionalRoot_le_one : exceptionalRoot ≤ 1 := by
  have hc : exceptionalRoot^3 = 3*1.0302*1.0033^2/Real.pi := cubeRoot_cube (by positivity)
  apply (pow_le_pow_iff_left₀ (cubeRoot_pos (by positivity)).le
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : 3 ≠ 0)).mp
  change exceptionalRoot^3 ≤ 1^3
  rw [hc, one_pow]
  exact (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_d20])

theorem exceptionalScale_le_base {N : ℕ} (hN : Real.exp 2000 ≤ (N:ℝ)) (beta : ℝ) :
    exceptionalScale N beta ≤ baseWeight N beta := by
  exact (mul_le_mul_of_nonneg_right exceptionalRoot_le_one
    (baseWeight_pos (nat_pos_of_exp_le hN) beta).le).trans_eq (one_mul _)

theorem radiusRoot_le_power {N q : ℕ} (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : 0 < q) :
    radiusRoot N q ≤ 0.6 * sourceL N * (q:ℝ)^(-(1:ℝ)/3) := by
  have hl := sourceL_pos hN
  have hc : ((q:ℝ)^(-(1:ℝ)/3))^3 = (q:ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    norm_num [Real.rpow_neg_one]
  apply (pow_le_pow_iff_left₀ (roots_pos hN hq).2.2.le
    (by positivity) (by norm_num : 3 ≠ 0)).mp
  rw [radiusRoot_cube_source hN hq]
  simp only [mul_pow, hc]
  have hpi : 3.36/(5*Real.pi) ≤ (0.6:ℝ)^3 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith [Real.pi_gt_d20])
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpi (pow_nonneg hl.le 3)) (by positivity)).trans_eq
      (by ring)

theorem root_times_originalMother {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : 0 < q) :
    radiusRoot N q * originalMotherBudget N q ≤
      0.6 * (q:ℝ)^(-(1:ℝ)/3) * (8.2e-10 + 0.063*q/sourceL N^3) := by
  have hl := sourceL_pos hN
  have hM : 0 ≤ originalMotherBudget N q := by unfold originalMotherBudget; positivity
  apply (mul_le_mul_of_nonneg_right (radiusRoot_le_power hN hq) hM).trans_eq
  unfold originalMotherBudget
  field_simp

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
