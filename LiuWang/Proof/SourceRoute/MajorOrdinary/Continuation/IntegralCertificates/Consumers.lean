import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.LowIntegral
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.HighIntegral
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.SourceTailAssembly

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates

theorem first_moment_with_finite_head {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment (sourceP N) (1 / 6) ≤ totientMoment 100000 (1 / 6) + 0.002500282 := by
  linarith only [source421_literal_initial_terms hN hRS, low_nuKernel_integral]

theorem second_moment_with_finite_head {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment (sourceP N) (7 / 6) ≤ totientMoment 100000 (7 / 6) + 8794 +
      nu (sourceP N) ^ 2 * 6 *
        ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) := by
  linarith only [source422_literal_initial_terms hN hRS, high_nuKernel_integral]

theorem I12_with_certified_fixed_integrals {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4)
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    ‖I12 N‖ ≤ linearPrefactor * (N : ℝ) ^ 2 *
      (0.0194 * (totientMoment 100000 (1 / 6) + 0.002500282) +
        (5 * 0.0126 / sourceL N ^ 3) *
          (totientMoment 100000 (7 / 6) + 8794 +
            nu (sourceP N) ^ 2 * 6 *
              ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)))) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  apply (I12_literal_initial_terms hN hlow hhigh hRS).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold linearPrefactor; positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    linarith only [low_nuKernel_integral]
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [high_nuKernel_integral]

theorem both_original_fixed_integrals :
    (∫ x in (100000 : ℝ)..10000000000, x ^ (-11 / 6 : ℝ) * nu x ^ 2) ≤ 0.0025 ∧
      (∫ x in (100000 : ℝ)..10000000000, x ^ (-5 / 6 : ℝ) * nu x ^ 2) ≤ 8794 :=
  ⟨original_low_fixed_integral, original_high_fixed_integral⟩

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
