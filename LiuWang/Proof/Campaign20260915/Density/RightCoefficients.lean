import LiuWang.Proof.NonprincipalDensityAdvance.Detector
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.Campaign20260915.Density

def largeDivisors (y : ℝ) (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => y ≤ (d : ℝ))

theorem coefficient_eq_large_divisor_tail (y : ℝ) (n : ℕ) :
    coefficient y n = -∑ d ∈ largeDivisors y n, (μ d : ℂ) := by
  have hsum := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] at hsum
  have hsplit := sum_filter_add_sum_filter_not n.divisors
    (fun d => (d : ℝ) < y) (fun d => (μ d : ℂ))
  rw [coefficient_apply, ← sum_filter, ← hsum, ← hsplit]
  simp only [not_lt, largeDivisors]
  ring

theorem coefficient_norm_le_large_divisors (y : ℝ) (n : ℕ) :
    ‖coefficient y n‖ ≤ (largeDivisors y n).card := by
  rw [coefficient_eq_large_divisor_tail, norm_neg]
  calc
    _ ≤ ∑ d ∈ largeDivisors y n, ‖(μ d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ largeDivisors y n, (1 : ℝ) := by
      apply sum_le_sum
      intro d _
      rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
    _ = _ := by simp

theorem twisted_coefficient_norm_le_large_divisors {q : ℕ} (chi : Character q)
    (y : ℝ) (n : ℕ) :
    ‖LiuWang.Proof.NonprincipalDensityAdvance.coefficient chi y n‖ ≤
      (largeDivisors y n).card := by
  rw [LiuWang.Proof.NonprincipalDensityAdvance.coefficient, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (chi.norm_le_one n)).trans
    (coefficient_norm_le_large_divisors y n)

theorem coefficient_sq_le_divisors_mul_tail (y : ℝ) (n : ℕ) :
    ‖coefficient y n‖ ^ 2 ≤
      (n.divisors.card : ℝ) * (largeDivisors y n).card := by
  have h := coefficient_norm_le_large_divisors y n
  have hsub : ((largeDivisors y n).card : ℝ) ≤ n.divisors.card :=
    Nat.cast_le.mpr (card_le_card (filter_subset _ _))
  nlinarith [norm_nonneg (coefficient y n)]

#print axioms coefficient_sq_le_divisors_mul_tail

end LiuWang.Proof.Campaign20260915.Density
