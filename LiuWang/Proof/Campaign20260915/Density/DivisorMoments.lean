import LiuWang.Proof.Campaign20260915.Density.DivisorCoordinates
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.TailFiniteMean
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.EulerSeries

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

namespace LiuWang.Proof.Campaign20260915.Density

theorem nat_mul_rpow (a b : ℕ) (s : ℝ) :
    ((a * b : ℕ) : ℝ) ^ s = (a : ℝ) ^ s * (b : ℝ) ^ s := by
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem divisor_square_prefix_power (X : ℕ) (s : ℝ) :
    (∑ n ∈ Icc 1 X, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)) ≤
      (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-s)) ^ 4 := by
  have h := large_divisor_square_weight_le X 0 (fun n => (n : ℝ) ^ (-s))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  simp only [largeDivisors, Nat.cast_nonneg, filter_true, true_and, ite_true] at h
  apply h.trans_eq
  simp_rw [nat_mul_rpow]
  simp only [← mul_sum, ← sum_mul]
  ring

theorem divisor_square_power {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {s : ℝ} (hs : 1 < s) :
    (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)) ≤
      (1 + 1 / (s - 1)) ^ 4 := by
  have hsub : S ⊆ Icc 1 (S.sup id) := by
    intro n hn
    exact mem_Icc.mpr ⟨hS n hn, le_sup (f := id) hn⟩
  have h := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
    (divisor_square_prefix_power (S.sup id) s)
  exact h.trans (pow_le_pow_left₀ (by positivity) (finite_power_sum _ hs) 4)

theorem divisor_square_log_power {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {d : ℝ} (hd : 0 < d) :
    (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 *
      (n : ℝ) ^ (-(1 + 2 * d)) * (3 + Real.log n)) ≤
      3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4 := by
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (n : ℝ) ^ (-(1 + 2 * d)) * Real.log n ≤
        (2 / d) * (n : ℝ) ^ (-(1 + (3 / 2) * d)) := by
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hS n hn)
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_rpow_div hn0.le (show 0 < d / 2 by linarith))
      (Real.rpow_nonneg hn0.le (-(1 + 2 * d)))
    apply h.trans_eq
    rw [← mul_div_assoc, ← Real.rpow_add hn0]
    rw [show -(1 + 2 * d) + d / 2 = -(1 + (3 / 2) * d) by ring]
    field_simp
  have h := sum_le_sum (fun n hn =>
    mul_le_mul_of_nonneg_left (hpoint n hn) (sq_nonneg (n.divisors.card : ℝ)))
  have h1 := divisor_square_power hS (show 1 < 1 + 2 * d by linarith)
  have h2 := mul_le_mul_of_nonneg_left
    (divisor_square_power hS (show 1 < 1 + (3 / 2) * d by linarith))
    (show 0 ≤ 2 / d by positivity)
  simp only [add_sub_cancel_left] at h1 h2
  have he : (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 *
      (n : ℝ) ^ (-(1 + 2 * d)) * (3 + Real.log n)) =
      3 * (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + 2 * d))) +
        ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 *
          ((n : ℝ) ^ (-(1 + 2 * d)) * Real.log n) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [he]
  have he2 : (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 *
      ((2 / d) * (n : ℝ) ^ (-(1 + (3 / 2) * d)))) =
      (2 / d) * ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 *
        (n : ℝ) ^ (-(1 + (3 / 2) * d)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [he2] at h
  linarith

#print axioms divisor_square_power
#print axioms divisor_square_log_power

end LiuWang.Proof.Campaign20260915.Density
