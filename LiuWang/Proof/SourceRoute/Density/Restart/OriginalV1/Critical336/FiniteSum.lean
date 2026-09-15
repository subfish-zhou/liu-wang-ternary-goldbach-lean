import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.EulerIdentity
import LiuWang.Proof.GlobalZeroDensity.CriticalLine

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336

theorem sum_inv_sqrt_inclusive (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, (Real.sqrt (m : ℝ))⁻¹) ≤ 2 * Real.sqrt n := by
  apply le_trans ?_ (LiuWang.Proof.GlobalZeroDensity.sum_inv_sqrt_succ_le n)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro m _ _
    positivity

theorem finite_critical_sum {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ ≤
      2 * Real.sqrt N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, ‖(n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (Real.sqrt (n : ℝ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by simp only [Finset.mem_Icc] at hn; omega)
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      norm_num
      rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
    _ ≤ 2 * Real.sqrt (⌊N⌋₊ : ℝ) := sum_inv_sqrt_inclusive _
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hN)) (by norm_num)

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336
