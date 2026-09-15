import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.WholeHeads
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.Source423Scalar

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads

theorem source421_with_certified_head {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment (sourceP N) (1 / 6) ≤ 3.2868 := by
  linarith only [first_moment_with_finite_head hN hRS, original_first_head]

theorem source422_with_certified_head {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment (sourceP N) (7 / 6) ≤ 8864 +
      6 * nu (sourceP N) ^ 2 *
        ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) := by
  linarith only [second_moment_with_finite_head hN hRS, original_second_head]

theorem I12_with_certified_heads_and_integrals {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4)
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    ‖I12 N‖ ≤ 0.1108 * (N : ℝ) ^ 2 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hpaid := I12_with_certified_fixed_integrals hN hlow hhigh hRS
  have hscalar := source423_scalar hN
  calc
    _ ≤ linearPrefactor * (N : ℝ) ^ 2 *
        (0.0194 * (totientMoment 100000 (1 / 6) + 0.002500282) +
          (5 * 0.0126 / sourceL N ^ 3) *
            (totientMoment 100000 (7 / 6) + 8794 +
              nu (sourceP N) ^ 2 * 6 *
                ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)))) := hpaid
    _ ≤ linearPrefactor * (N : ℝ) ^ 2 *
        (0.0194 * 3.2868 + (5 * 0.0126 / sourceL N ^ 3) *
          (8864 + 6 * nu (sourceP N) ^ 2 *
            ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold linearPrefactor; positivity)
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith only [original_first_head]
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [original_second_head]
    _ = (linearPrefactor *
        (0.0194 * 3.2868 + (5 * 0.0126 / sourceL N ^ 3) *
          (8864 + 6 * nu (sourceP N) ^ 2 *
            ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ))))) * (N : ℝ) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads
