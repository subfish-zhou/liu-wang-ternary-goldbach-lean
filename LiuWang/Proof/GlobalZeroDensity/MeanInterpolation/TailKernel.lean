import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.ThreeLines

/-! A cutoff-independent near/far logarithmic kernel bound for right-half-plane tails. -/

set_option autoImplicit false

noncomputable section

open Finset
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

def tailKernel (σ : ℝ) (m n : ℕ) : ℝ :=
  (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log m - Real.log n|

theorem tailKernel_symm (σ : ℝ) (m n : ℕ) : tailKernel σ m n = tailKernel σ n m := by
  simp only [tailKernel, abs_sub_comm, mul_comm]

theorem tailKernel_near {σ : ℝ} (hσ : 1 < σ) {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    tailKernel σ m n ≤ (m : ℝ) ^ (1 - 2 * σ) / |(m : ℝ) - n| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn0 : (m : ℝ) < n := by exact_mod_cast hmn
  have hn0 := hm0.trans hmn0
  have hlog := Real.log_le_sub_one_of_pos (div_pos hm0 hn0)
  rw [Real.log_div hm0.ne' hn0.ne'] at hlog
  have hL : 0 < Real.log n - Real.log m := sub_pos.mpr (Real.log_lt_log hm0 hmn0)
  have hgap : ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := by
    have he : ((n : ℝ) - m) / n = 1 - (m : ℝ) / n := by field_simp
    rw [he]; linarith
  have hrec := one_div_le_one_div_of_le (div_pos (sub_pos.mpr hmn0) hn0) hgap
  have hp := Real.rpow_le_rpow_of_nonpos hm0 hmn0.le (by linarith : 1 - σ ≤ 0)
  have he : (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) * (1 / (((n : ℝ) - m) / n)) =
      (m : ℝ) ^ (-σ) * (n : ℝ) ^ (1 - σ) / ((n : ℝ) - m) := by
    rw [show 1 - σ = -σ + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    field_simp
  have he' : (m : ℝ) ^ (-σ) * (m : ℝ) ^ (1 - σ) = (m : ℝ) ^ (1 - 2 * σ) := by
    rw [← Real.rpow_add hm0]
    congr 1; ring
  unfold tailKernel
  rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hm0 hmn0)), neg_sub,
    abs_of_neg (sub_neg.mpr hmn0), neg_sub]
  calc
    _ ≤ (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) * (1 / (((n : ℝ) - m) / n)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hrec (by positivity : 0 ≤ (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
    _ = _ := he
    _ ≤ (m : ℝ) ^ (-σ) * (m : ℝ) ^ (1 - σ) / ((n : ℝ) - m) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by linarith)
    _ = _ := by rw [he']

theorem tailKernel_far {σ : ℝ} {m n : ℕ} (hm : 0 < m) (hmn : 2 * m < n) :
    tailKernel σ m n ≤ 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn0 : 2 * (m : ℝ) < n := by exact_mod_cast hmn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hm0 hn0)
  rw [Real.log_div hm0.ne' hn0.ne'] at hlog
  have hhalf : (m : ℝ) / n ≤ 1 / 2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hL : 1 / 2 ≤ |Real.log m - Real.log n| := by
    rw [abs_of_neg (by linarith : Real.log m - Real.log n < 0)]
    linarith
  have hrec := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hL
  have h := mul_le_mul_of_nonneg_left hrec
    (by positivity : 0 ≤ (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
  unfold tailKernel
  norm_num at h
  simp only [div_eq_mul_inv]
  nlinarith

theorem near_gap_sum (S : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ S.filter (fun n => m < n ∧ n ≤ 2 * m), 1 / |(m : ℝ) - n|) ≤
      2 * (3 + Real.log m) := by
  have hsub : S.filter (fun n => m < n ∧ n ≤ 2 * m) ⊆ range (2 * m + 1) := by
    intro n hn
    have := (mem_filter.mp hn).2.2
    simp only [mem_range]
    omega
  have hsum := sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => by positivity : ∀ n ∈ range (2 * m + 1),
      n ∉ S.filter (fun n => m < n ∧ n ≤ 2 * m) → 0 ≤ 1 / |(m : ℝ) - n|)
  have hgap := reciprocal_gap_row (m := m) (N := 2 * m + 1) (by omega)
  have hH := inverse_range_le_log (2 * m + 1)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log (2 * m + 1 : ℕ) ≤ 2 + Real.log m := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * m + 1)
      (show (2 * m + 1 : ℝ) ≤ 3 * m by exact_mod_cast (show 2 * m + 1 ≤ 3 * m by omega))
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hm0.ne'] at h
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    push_cast
    linarith
  nlinarith

theorem kernel_row_bound (S : Finset ℕ) {σ : ℝ} (hσ : 1 < σ)
    {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ S.filter (fun n => m < n), tailKernel σ m n) ≤
      2 * (m : ℝ) ^ (1 - 2 * σ) * (3 + Real.log m) +
        2 * (m : ℝ) ^ (-σ) * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by
  have hsplit := sum_filter_add_sum_filter_not (S.filter (fun n => m < n))
    (fun n => n ≤ 2 * m) (tailKernel σ m)
  have hnear :
      (∑ n ∈ (S.filter (fun n => m < n)).filter (fun n => n ≤ 2 * m), tailKernel σ m n) ≤
        2 * (m : ℝ) ^ (1 - 2 * σ) * (3 + Real.log m) := by
    rw [filter_filter]
    calc
      _ ≤ ∑ n ∈ S.filter (fun n => m < n ∧ n ≤ 2 * m),
          (m : ℝ) ^ (1 - 2 * σ) / |(m : ℝ) - n| := by
        exact sum_le_sum (fun n hn => tailKernel_near hσ hm (mem_filter.mp hn).2.1)
      _ = (m : ℝ) ^ (1 - 2 * σ) *
          ∑ n ∈ S.filter (fun n => m < n ∧ n ≤ 2 * m), 1 / |(m : ℝ) - n| := by
        rw [mul_sum]; apply sum_congr rfl; intro n _; ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (near_gap_sum S hm)
          (Real.rpow_nonneg (Nat.cast_nonneg m) (1 - 2 * σ))
        nlinarith
  have hfar :
      (∑ n ∈ (S.filter (fun n => m < n)).filter (fun n => ¬n ≤ 2 * m), tailKernel σ m n) ≤
        2 * (m : ℝ) ^ (-σ) * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by
    calc
      _ ≤ ∑ n ∈ (S.filter (fun n => m < n)).filter (fun n => ¬n ≤ 2 * m),
          2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) :=
        sum_le_sum (fun n hn => tailKernel_far hm (Nat.lt_of_not_ge (mem_filter.mp hn).2))
      _ ≤ ∑ n ∈ S, 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) :=
        sum_le_sum_of_subset_of_nonneg (by intro n hn; exact (mem_filter.mp (mem_filter.mp hn).1).1)
          (fun _ _ _ => by positivity)
      _ = _ := by rw [mul_sum]
  linarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
