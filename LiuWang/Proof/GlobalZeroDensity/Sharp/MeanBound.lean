import LiuWang.Proof.GlobalZeroDensity.Sharp.HarmonicGaps

/-! An unconditional logarithmic-order mean bound for the actual strict-cutoff mollifier. -/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem norm_criticalCoefficient_le {n : ℕ} (hn : 0 < n) :
    ‖criticalCoefficient n‖ ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  rw [norm_criticalCoefficient hn, ← one_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

theorem coefficient_gap_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hne : m ≠ n) :
    ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n| ≤
      1 / |(m : ℝ) - n| + 1 / (2 * Real.sqrt m * Real.sqrt n) := by
  have hp := mul_le_mul (norm_criticalCoefficient_le hm) (norm_criticalCoefficient_le hn)
    (norm_nonneg _) (by positivity)
  have h := div_le_div_of_nonneg_right hp (abs_nonneg (Real.log m - Real.log n))
  have hk := logarithmic_kernel_abs_le (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
    (by exact_mod_cast hne : (m : ℝ) ≠ n)
  apply le_trans h
  simpa only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hk

theorem smooth_kernel_sum_le (N : ℕ) :
    (∑ m ∈ range N, ∑ n ∈ range N,
      1 / (2 * Real.sqrt m * Real.sqrt n)) ≤ 2 * N := by
  have he (m n : ℕ) : 1 / (2 * Real.sqrt m * Real.sqrt n) =
      (1 / 2) * (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ := by
    simp only [one_div, mul_inv_rev]
    ring
  simp_rw [he, ← mul_sum]
  rw [← sum_mul, ← mul_sum]
  have h := pow_le_pow_left₀
    (sum_nonneg (fun n (_ : n ∈ range N) => inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ))))
    (sum_inv_sqrt_le N) 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at h
  nlinarith

theorem mollifier_energy_le_inverse_range (N : ℕ) :
    (∑ n ∈ (range N).erase 0, (ArithmeticFunction.moebius n : ℝ) ^ 2 / n) ≤
      ∑ n ∈ range N, (n : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ n ∈ (range N).erase 0, (n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n _
      rw [← one_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)

theorem off_diagonal_sum_le (N : ℕ) :
    (∑ m ∈ (range N).erase 0, ∑ n ∈ ((range N).erase 0).erase m,
      ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) ≤
      2 * N * (∑ k ∈ range N, (k : ℝ)⁻¹) + 2 * N := by
  let K (m n : ℕ) : ℝ := 1 / |(m : ℝ) - n| + 1 / (2 * Real.sqrt m * Real.sqrt n)
  have hK (m n : ℕ) : 0 ≤ K m n := by dsimp [K]; positivity
  have hlarge :
      (∑ m ∈ (range N).erase 0, ∑ n ∈ ((range N).erase 0).erase m,
        ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) ≤
        ∑ m ∈ range N, ∑ n ∈ range N, K m n := by
    calc
      _ ≤ ∑ m ∈ (range N).erase 0, ∑ n ∈ ((range N).erase 0).erase m, K m n := by
        apply sum_le_sum
        intro m hm
        apply sum_le_sum
        intro n hn
        exact coefficient_gap_le (Nat.pos_of_ne_zero (mem_erase.mp hm).1)
          (Nat.pos_of_ne_zero (mem_erase.mp (mem_erase.mp hn).2).1)
          (mem_erase.mp hn).1.symm
      _ ≤ ∑ m ∈ (range N).erase 0, ∑ n ∈ range N, K m n := by
        apply sum_le_sum
        intro m _
        exact sum_le_sum_of_subset_of_nonneg
          ((erase_subset _ _).trans (erase_subset _ _)) (fun n _ _ => hK m n)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
        (fun m _ _ => sum_nonneg (fun n _ => hK m n))
  have hgap : (∑ m ∈ range N, ∑ n ∈ range N, 1 / |(m : ℝ) - n|) ≤
      2 * N * ∑ k ∈ range N, (k : ℝ)⁻¹ := by
    have h := sum_le_sum (fun m (hm : m ∈ range N) => reciprocal_gap_row (mem_range.mp hm))
    simp only [sum_const, card_range, nsmul_eq_mul] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hsmooth := smooth_kernel_sum_le N
  dsimp [K] at hlarge
  simp only [sum_add_distrib] at hlarge
  linarith

theorem Q_mean_le (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in -u..u, ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      (2 * u + 4 * (⌈y⌉₊ : ℝ)) * (1 + Real.log ⌈y⌉₊) + 4 * (⌈y⌉₊ : ℝ) := by
  have he := mollifier_energy_le_inverse_range ⌈y⌉₊
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * u by positivity)
  have ho := off_diagonal_sum_le ⌈y⌉₊
  have h := Q_mean_diagonal_offDiagonal y hu
  have hlog := mul_le_mul_of_nonneg_left (inverse_range_le_log ⌈y⌉₊)
    (show 0 ≤ 2 * u + 4 * (⌈y⌉₊ : ℝ) by positivity)
  nlinarith

end LiuWang.Proof.GlobalZeroDensity.Sharp
