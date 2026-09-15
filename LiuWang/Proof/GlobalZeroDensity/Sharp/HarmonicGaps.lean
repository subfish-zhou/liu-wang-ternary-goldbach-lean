import LiuWang.Proof.GlobalZeroDensity.Sharp.LogKernel

/-! Summing the off-diagonal gaps without replacing them by the smallest gap. -/

set_option autoImplicit false

noncomputable section

open Finset

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem reciprocal_gap_row {N m : ℕ} (hm : m < N) :
    (∑ n ∈ range N, 1 / |(m : ℝ) - n|) ≤
      2 * ∑ k ∈ range N, (k : ℝ)⁻¹ := by
  let A := (range N).filter (fun n => n < m)
  let B := (range N).filter (fun n => ¬ n < m)
  have hA : A.image (fun n => m - n) ⊆ range N := by
    intro k hk
    obtain ⟨n, _, rfl⟩ := mem_image.mp hk
    rw [mem_range]
    omega
  have hB : B.image (fun n => n - m) ⊆ range N := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hnN : n < N := mem_range.mp (mem_filter.mp hn).1
    rw [mem_range]
    omega
  have hleft : (∑ n ∈ A, 1 / |(m : ℝ) - n|) ≤ ∑ k ∈ range N, (k : ℝ)⁻¹ := by
    have he : (∑ n ∈ A, 1 / |(m : ℝ) - n|) =
        ∑ k ∈ A.image (fun n => m - n), (k : ℝ)⁻¹ := by
      rw [sum_image (fun a ha b hb h => by
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        omega)]
      apply sum_congr rfl
      intro n hn
      have hn' : n < m := (mem_filter.mp hn).2
      have hreal : (n : ℝ) ≤ m := by exact_mod_cast hn'.le
      rw [Nat.cast_sub hn'.le, abs_of_nonneg (by linarith),
        one_div]
    rw [he]
    exact sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => by positivity)
  have hright : (∑ n ∈ B, 1 / |(m : ℝ) - n|) ≤ ∑ k ∈ range N, (k : ℝ)⁻¹ := by
    have he : (∑ n ∈ B, 1 / |(m : ℝ) - n|) =
        ∑ k ∈ B.image (fun n => n - m), (k : ℝ)⁻¹ := by
      rw [sum_image (fun a ha b hb h => by
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        omega)]
      apply sum_congr rfl
      intro n hn
      have hn' : m ≤ n := Nat.le_of_not_gt (mem_filter.mp hn).2
      have hreal : (m : ℝ) ≤ n := by exact_mod_cast hn'
      rw [Nat.cast_sub hn', abs_of_nonpos (by linarith), neg_sub, one_div]
    rw [he]
    exact sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => by positivity)
  have he := sum_filter_add_sum_filter_not (range N) (fun n => n < m)
    (fun n => 1 / |(m : ℝ) - n|)
  change (∑ n ∈ A, _) + (∑ n ∈ B, _) = _ at he
  linarith

theorem inverse_range_le_log (N : ℕ) :
    (∑ n ∈ range N, (n : ℝ)⁻¹) ≤ 1 + Real.log N := by
  have he : (∑ n ∈ range (N + 1), (n : ℝ)⁻¹) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega : 1 ≤ N + 1)]
    simp
  have h := harmonic_le_one_add_log N
  rw [← he, sum_range_succ] at h
  exact (le_add_of_nonneg_right (by positivity)).trans h

end LiuWang.Proof.GlobalZeroDensity.Sharp
