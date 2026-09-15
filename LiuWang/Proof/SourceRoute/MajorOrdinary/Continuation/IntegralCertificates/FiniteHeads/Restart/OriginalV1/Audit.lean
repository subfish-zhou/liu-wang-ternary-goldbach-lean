import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.TotientTail
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.OriginalArithmetic

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

example : 0 < nu 3 := nu_pos_of_three_le le_rfl

example {y : ℝ} (hy : 27 ≤ y) : nu 27 ≤ nu y :=
  nu_monotone_27 (by norm_num) (by simpa only [Set.mem_Ici] using hy) hy

example :
    (1 : ℝ) / (Nat.totient 1 : ℝ) ≤ nu 27 ∧
      (2 : ℝ) / (Nat.totient 2 : ℝ) ≤ nu 27 :=
  small_totient_ratios (by norm_num)

example (f : ℕ → ℝ) : (∑ q ∈ Finset.Icc 1001 ⌊(1000.5 : ℝ)⌋₊, f q) = 0 := by
  norm_num

example : weightedTotientSum (1000.5 : ℝ) = weightedTotientSum 1000 := by
  have h := weighted_totient_sum_split (by norm_num : (1000 : ℝ) ≤ 1000.5)
  norm_num at h ⊢
  exact h

example :
    6 * nu 10000000000 ^ 2 *
      ((10000000000 : ℝ) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) = 0 := by
  rw [ten_billion_sixth_root, sub_self, mul_zero]

example
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    linearPrefactor *
      (0.0194 * totientMoment ((3100 : ℝ) ^ 3) (1 / 6) +
        (5 * 0.0126 / (3100 : ℝ) ^ 3) *
          totientMoment ((3100 : ℝ) ^ 3) (7 / 6)) ≤ 0.1108 :=
  source423_arithmetic le_rfl hRS

set_option pp.fullNames true

#print nu
#print nuKernel
#print totientWeight
#print totientMoment
#print lowWeightSum
#print highWeightSum
#print linearPrefactor

#check @loglog_pos_of_three_le
#print axioms loglog_pos_of_three_le
#check @two_le_nu
#print axioms two_le_nu
#check @nu_pos_of_three_le
#print axioms nu_pos_of_three_le
#check @nu_monotone_27
#print axioms nu_monotone_27

#check @small_totient_ratios
#print axioms small_totient_ratios
#check @totient_ratio_le_nu_cutoff
#print axioms totient_ratio_le_nu_cutoff
#check @weighted_totient_tail
#print axioms weighted_totient_tail
#check @weighted_totient_sum_split
#print axioms weighted_totient_sum_split
#check @weighted_totient_sum_original
#print axioms weighted_totient_sum_original
#check @R14_bound
#print axioms R14_bound
#check @I11_source46_with_R14
#print axioms I11_source46_with_R14

#check @source419_real_tail
#print axioms source419_real_tail
#check @source422_real_tail
#print axioms source422_real_tail
#check @source421_real_cutoff
#print axioms source421_real_cutoff
#check @source422_real_cutoff
#print axioms source422_real_cutoff
#check @source423_scalar_real_cutoff
#print axioms source423_scalar_real_cutoff
#check @source423_arithmetic
#print axioms source423_arithmetic
#check @I12_original_arithmetic_consumer
#print axioms I12_original_arithmetic_consumer

#check @original_first_head
#print axioms original_first_head
#check @original_second_head
#print axioms original_second_head
#check @original_low_fixed_integral
#print axioms original_low_fixed_integral
#check @original_high_fixed_integral
#print axioms original_high_fixed_integral
#check @nu_le_source_power
#print axioms nu_le_source_power
#check @low_power_integral_le
#print axioms low_power_integral_le
#check @high_finite_tail_le
#print axioms high_finite_tail_le
#check @I12_source417
#print axioms I12_source417
#check @LiuWang.Proof.ArithmeticBounds.sum_moebius_totient_square_le_1961
#print axioms LiuWang.Proof.ArithmeticBounds.sum_moebius_totient_square_le_1961

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1
