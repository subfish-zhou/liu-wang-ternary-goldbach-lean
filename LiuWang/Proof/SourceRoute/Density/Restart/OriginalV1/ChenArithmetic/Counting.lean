import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.SquareDivisors
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.EulerSeries

set_option autoImplicit false
noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

theorem squarefreeCount_truncation_error {y : ℝ} (hy : 1 ≤ y) :
    |squarefreeCount y - y * ∑ d ∈ positiveBelow (Real.sqrt y),
      (μ d : ℝ) / (d : ℝ) ^ 2| ≤ Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  rw [squarefreeCount_eq_strict_multiples, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    (∑ d ∈ positiveBelow (Real.sqrt y),
        |(μ d : ℝ) * ((positiveBelow (y / (d : ℝ) ^ 2)).card : ℝ) -
          y * ((μ d : ℝ) / (d : ℝ) ^ 2)|) ≤
        ∑ _d ∈ positiveBelow (Real.sqrt y), (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (mem_positiveBelow.mp hd).1
      have hb := positiveBelow_card_bounds (div_pos hy0 (sq_pos_of_pos hd0))
      have he : |((positiveBelow (y / (d : ℝ) ^ 2)).card : ℝ) -
          y / (d : ℝ) ^ 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hm : |(μ d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      have hf : (μ d : ℝ) * ((positiveBelow (y / (d : ℝ) ^ 2)).card : ℝ) -
          y * ((μ d : ℝ) / (d : ℝ) ^ 2) =
          (μ d : ℝ) * (((positiveBelow (y / (d : ℝ) ^ 2)).card : ℝ) -
            y / (d : ℝ) ^ 2) := by ring
      rw [hf, abs_mul]
      exact (mul_le_mul hm he (abs_nonneg _) (by norm_num)).trans (by norm_num)
    _ ≤ Real.sqrt y := by
      simpa using (positiveBelow_card_bounds (Real.sqrt_pos.mpr hy0)).2

theorem moebius_sqrt_cutoff_error {y : ℝ} (hy : 1 ≤ y) :
    |(∑ d ∈ positiveBelow (Real.sqrt y), (μ d : ℝ) / (d : ℝ) ^ 2) -
      6 / Real.pi ^ 2| ≤ 1 / y + 1 / Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hc : Real.sqrt y ≤ (⌈Real.sqrt y⌉₊ : ℝ) := Nat.le_ceil _
  have hc0 : 0 < ⌈Real.sqrt y⌉₊ := Nat.ceil_pos.mpr hs0
  have he : (∑ d ∈ positiveBelow (Real.sqrt y), (μ d : ℝ) / (d : ℝ) ^ 2) =
      ∑ d ∈ range ⌈Real.sqrt y⌉₊, (μ d : ℝ) / (d : ℝ) ^ 2 := by
    rw [positiveBelow, sum_Ico_eq_sub _ (by omega)]
    simp
  rw [he]
  apply (moebius_div_sq_tail hc0).trans
  have hsq : y ≤ (⌈Real.sqrt y⌉₊ : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt hy0.le, Real.sqrt_nonneg y]
  exact add_le_add (one_div_le_one_div_of_le hy0 hsq)
    (one_div_le_one_div_of_le hs0 hc)

theorem equation_10 {y : ℝ} (hy : 1 ≤ y) :
    |squarefreeCount y - 6 * y / Real.pi ^ 2| ≤ 1 + 2 * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  let S := ∑ d ∈ positiveBelow (Real.sqrt y), (μ d : ℝ) / (d : ℝ) ^ 2
  have h1 := squarefreeCount_truncation_error hy
  have h2 := mul_le_mul_of_nonneg_left (moebius_sqrt_cutoff_error hy) hy0.le
  have he : y * (1 / y + 1 / Real.sqrt y) = 1 + Real.sqrt y := by
    field_simp
    nlinarith [Real.sq_sqrt hy0.le]
  rw [he] at h2
  calc
    |squarefreeCount y - 6 * y / Real.pi ^ 2| =
        |(squarefreeCount y - y * S) + y * (S - 6 / Real.pi ^ 2)| := by
      congr 1; dsimp [S]; ring
    _ ≤ |squarefreeCount y - y * S| + |y * (S - 6 / Real.pi ^ 2)| := abs_add_le _ _
    _ ≤ Real.sqrt y + (1 + Real.sqrt y) := by
      rw [abs_mul, abs_of_pos hy0]
      exact add_le_add h1 h2
    _ = 1 + 2 * Real.sqrt y := by ring

theorem squarefreeCount_upper {y : ℝ} (hy : 1 ≤ y) :
    squarefreeCount y ≤ 6 / Real.pi ^ 2 * y + 2 * Real.sqrt y + 1 := by
  have h := (abs_le.mp (equation_10 hy)).2
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
