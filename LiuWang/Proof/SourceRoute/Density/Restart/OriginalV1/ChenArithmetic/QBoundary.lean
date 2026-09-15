import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.WeightedBounds
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.SourceComparison

set_option autoImplicit false
noncomputable section

open Finset Complex
open scoped ArithmeticFunction.Moebius
open LiuWang.Proof.GlobalZeroDensity

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

theorem Q_eq_positiveBelow {y : ℝ} (hy : 0 < y) (s : ℂ) :
    Q y s = ∑ n ∈ positiveBelow y, (μ n : ℂ) / (n : ℂ) ^ s := by
  have hc : 1 ≤ ⌈y⌉₊ := Nat.ceil_pos.mpr hy
  rw [positiveBelow, sum_Ico_eq_sub _ hc]
  simp [Q]

theorem norm_Q_le_weighted_sum {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖Q y s‖ ≤ ∑ n ∈ positiveBelow y, |(μ n : ℝ)| / (n : ℝ) ^ s.re := by
  rw [Q_eq_positiveBelow hy]
  apply (norm_sum_le _ _).trans_eq
  apply sum_congr rfl
  intro n hn
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (mem_positiveBelow.mp hn).1]
  congr 1
  norm_cast

theorem norm_Q_half_from_equation_11 {y : ℝ} (hy : 1 ≤ y) (t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * I)‖ ≤
      1.216 * Real.sqrt y + Real.log y + 2.4 := by
  have h := norm_Q_le_weighted_sum (show 0 < y by linarith) ((1 / 2 : ℂ) + t * I)
  have he : (((1 / 2 : ℂ) + t * I).re) = 1 / 2 := by simp
  rw [he] at h
  simp only [← Real.sqrt_eq_rpow] at h
  exact h.trans (equation_11 hy)

theorem norm_Q_one_from_equation_12 {y : ℝ} (hy : 1 ≤ y) (t : ℝ) :
    ‖Q y ((1 : ℂ) + t * I)‖ ≤ 0.608 * Real.log y + 5.608 := by
  have h := norm_Q_le_weighted_sum (show 0 < y by linarith) ((1 : ℂ) + t * I)
  have he : (((1 : ℂ) + t * I).re) = 1 := by simp
  rw [he] at h
  simp only [Real.rpow_one] at h
  exact h.trans (equation_12 hy)

theorem norm_Q_half {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) (t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * I)‖ ≤ 1.3071 * Real.sqrt y :=
  (norm_Q_half_from_equation_11 (by linarith [source_height_lower hy]) t).trans
    (sqrt_boundary_scalar hy)

theorem norm_Q_one {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) (t : ℝ) :
    ‖Q y ((1 : ℂ) + t * I)‖ ≤ 1.19 * Real.log y :=
  (norm_Q_one_from_equation_12 (by linarith [source_height_lower hy]) t).trans
    (harmonic_boundary_scalar hy)

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
