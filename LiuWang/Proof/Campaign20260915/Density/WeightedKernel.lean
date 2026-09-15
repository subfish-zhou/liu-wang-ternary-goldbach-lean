import LiuWang.Proof.Campaign20260915.Density.RightDiagonal
import LiuWang.Proof.GlobalZeroDensity.Sharp.LogKernel

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

namespace LiuWang.Proof.Campaign20260915.Density

def nearGap (m n : ℕ) : ℝ :=
  if n ≤ 2 * m ∧ m ≤ 2 * n then 1 / |(m : ℝ) - n| else 0

theorem nearGap_nonneg (m n : ℕ) : 0 ≤ nearGap m n := by
  unfold nearGap
  split_ifs <;> positivity

theorem nearGap_symm (m n : ℕ) : nearGap m n = nearGap n m := by
  simp only [nearGap, and_comm, abs_sub_comm]

theorem nearGap_row (S : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ S, nearGap m n) ≤ 2 * (3 + Real.log m) := by
  have hsub : S.filter (fun n => n ≤ 2 * m ∧ m ≤ 2 * n) ⊆ range (2 * m + 1) := by
    intro n hn
    have := (mem_filter.mp hn).2.1
    simpa only [mem_range] using Nat.lt_succ_of_le this
  have hsum := sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => by positivity : ∀ n ∈ range (2 * m + 1),
      n ∉ S.filter (fun n => n ≤ 2 * m ∧ m ≤ 2 * n) → 0 ≤ 1 / |(m : ℝ) - n|)
  have hgap := reciprocal_gap_row (m := m) (N := 2 * m + 1) (by omega)
  have hH := inverse_range_le_log (2 * m + 1)
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : Real.log (2 * m + 1 : ℕ) ≤ 2 + Real.log m := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * m + 1)
      (show (2 * m + 1 : ℝ) ≤ 3 * m by
        exact_mod_cast (show 2 * m + 1 ≤ 3 * m by omega))
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hm0.ne'] at h
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    push_cast
    linarith
  simp only [nearGap, ← sum_filter]
  nlinarith

theorem weighted_log_kernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b / |Real.log m - Real.log n| ≤
      ((m : ℝ) * a ^ 2 + (n : ℝ) * b ^ 2) / 2 * nearGap m n + 2 * a * b := by
  by_cases he : m = n
  · subst n
    simp only [sub_self, abs_zero, div_zero]
    have := nearGap_nonneg m m
    positivity
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmn : (m : ℝ) ≠ n := by exact_mod_cast he
  by_cases hnear : n ≤ 2 * m ∧ m ≤ 2 * n
  · rw [nearGap, if_pos hnear]
    have hh := logarithmic_kernel_abs_le hm0 hn0 hmn
    have hprod : 0 ≤ Real.sqrt m * Real.sqrt n * (a * b) := by positivity
    have h := mul_le_mul_of_nonneg_left hh hprod
    have hma := Real.sq_sqrt hm0.le
    have hnb := Real.sq_sqrt hn0.le
    have hs : Real.sqrt m * Real.sqrt n * (a * b) ≤
        ((m : ℝ) * a ^ 2 + (n : ℝ) * b ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt m * a - Real.sqrt n * b)]
    have hfirst := mul_le_mul_of_nonneg_right hs
      (show 0 ≤ 1 / |(m : ℝ) - n| by positivity)
    have he1 : Real.sqrt m * Real.sqrt n * (a * b) *
        (1 / (Real.sqrt m * Real.sqrt n * |Real.log m - Real.log n|)) =
        a * b / |Real.log m - Real.log n| := by
      field_simp
    have he2 : Real.sqrt m * Real.sqrt n * (a * b) *
        (1 / |(m : ℝ) - n| + 1 / (2 * Real.sqrt m * Real.sqrt n)) =
        Real.sqrt m * Real.sqrt n * (a * b) * (1 / |(m : ℝ) - n|) + a * b / 2 := by
      field_simp
    rw [he1, he2] at h
    nlinarith [mul_nonneg ha hb]
  · rw [nearGap, if_neg hnear, mul_zero, zero_add]
    have hrec : 1 / |Real.log m - Real.log n| ≤ 2 := by
      rcases not_and_or.mp hnear with h | h
      · simpa [tailKernel] using
          tailKernel_far (σ := 0) hm (Nat.lt_of_not_ge h)
      · simpa [tailKernel, abs_sub_comm] using
          tailKernel_far (σ := 0) hn (Nat.lt_of_not_ge h)
    have h := mul_le_mul_of_nonneg_left hrec (mul_nonneg ha hb)
    simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using h

theorem weighted_off_diagonal_rows (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (A : ℕ → ℝ) (hA : ∀ n ∈ S, 0 ≤ A n) (R : ℕ → ℝ)
    (hR : ∀ m ∈ S, (∑ n ∈ S, nearGap m n) ≤ R m) :
    (∑ m ∈ S, ∑ n ∈ S, A m * A n / |Real.log m - Real.log n|) ≤
      (∑ n ∈ S, (n : ℝ) * A n ^ 2 * R n) +
        2 * (∑ n ∈ S, A n) ^ 2 := by
  have h := sum_le_sum (fun m hm => sum_le_sum (fun n hn =>
    weighted_log_kernel (hS m hm) (hS n hn) (hA m hm) (hA n hn)))
  have hswap :
      (∑ m ∈ S, ∑ n ∈ S, (n : ℝ) * A n ^ 2 * nearGap m n) =
        ∑ m ∈ S, ∑ n ∈ S, (m : ℝ) * A m ^ 2 * nearGap m n := by
    rw [sum_comm]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    rw [nearGap_symm]
  have he (m n : ℕ) :
      ((m : ℝ) * A m ^ 2 + (n : ℝ) * A n ^ 2) / 2 * nearGap m n +
          2 * A m * A n =
        (1 / 2) * ((m : ℝ) * A m ^ 2 * nearGap m n) +
          (1 / 2) * ((n : ℝ) * A n ^ 2 * nearGap m n) + 2 * A m * A n := by ring
  simp_rw [he] at h
  simp only [sum_add_distrib, ← mul_sum] at h
  rw [hswap] at h
  have hrows := sum_le_sum (fun m hm =>
    mul_le_mul_of_nonneg_left (hR m hm)
      (show 0 ≤ (m : ℝ) * A m ^ 2 by positivity))
  have heq : (∑ m ∈ S, ∑ n ∈ S, (m : ℝ) * A m ^ 2 * nearGap m n) =
      ∑ m ∈ S, (m : ℝ) * A m ^ 2 * ∑ n ∈ S, nearGap m n := by
    simp only [mul_sum]
  simp only [← mul_sum, ← sum_mul] at h
  rw [← heq] at hrows
  simp only [← mul_sum] at hrows
  nlinarith

theorem weighted_off_diagonal (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (A : ℕ → ℝ) (hA : ∀ n ∈ S, 0 ≤ A n) :
    (∑ m ∈ S, ∑ n ∈ S, A m * A n / |Real.log m - Real.log n|) ≤
      2 * (∑ n ∈ S, (n : ℝ) * A n ^ 2 * (3 + Real.log n)) +
        2 * (∑ n ∈ S, A n) ^ 2 := by
  have h := weighted_off_diagonal_rows S hS A hA
    (fun m => 2 * (3 + Real.log m)) (fun m hm => nearGap_row S (hS m hm))
  convert h using 1
  rw [mul_sum]
  congr 1
  exact sum_congr rfl (fun _ _ => by ring)

#print axioms weighted_off_diagonal

end LiuWang.Proof.Campaign20260915.Density
