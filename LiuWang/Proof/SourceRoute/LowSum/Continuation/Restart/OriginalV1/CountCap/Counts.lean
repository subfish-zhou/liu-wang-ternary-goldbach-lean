import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.Negative

set_option autoImplicit false
noncomputable section
open Complex
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap

theorem original_T1_product_count_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    (∑ z ∈ productZeroValues q (1 - 0.26213 / Real.log x) (x / q),
      analyticOrderNatAt (productL q) z) ≤ 4 := by
  by_contra hn
  obtain ⟨p, r, u, _, hnonneg⟩ := original_product_to_2_28 hx hq (lt_of_not_ge hn)
    hRS hgammaHigh hgammaLow
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have hu := mem_strictZeroValues.mp u.zero_mem
  have hneg := original_2_28_negative hx hp.2.2.2.1 hr.2.2.2.1 hu.2.2.2.1
    hp.2.2.1.le hr.2.2.1.le hu.2.2.1.le
  exact (not_lt_of_ge hnonneg) hneg

theorem original_T1_strict_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    strictFamilyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 := by
  rw [strictFamilyCount_eq_product_count]
  exact original_T1_product_count_le_four hx hq hRS hgammaHigh hgammaLow

theorem original_T1_slot_card_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    Fintype.card (ZeroSlots q (1 - 0.26213 / Real.log x) (x / q)) ≤ 4 := by
  rw [card_zeroSlots]
  exact original_T1_strict_family_le_four hx hq hRS hgammaHigh hgammaLow

theorem closed_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    familyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 := by
  by_contra hn
  obtain ⟨p, r, u, _, hnonneg⟩ := original_closed_family_to_2_28 hx hq (lt_of_not_ge hn)
    hRS hgammaHigh hgammaLow
  have hp := mem_strictZeroValues.mp p.val.zero_mem
  have hr := mem_strictZeroValues.mp r.val.zero_mem
  have hu := mem_strictZeroValues.mp u.val.zero_mem
  have hneg := original_2_28_negative hx hp.2.2.2.1 hr.2.2.2.1 hu.2.2.2.1
    p.property r.property u.property
  exact (not_lt_of_ge hnonneg) hneg

theorem closed_slot_card_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    Fintype.card (ClosedSlots q (1 - 0.26213 / Real.log x) (x / q)) ≤ 4 := by
  rw [closedSlots_card]
  exact closed_family_le_four hx hq hRS hgammaHigh hgammaLow

theorem closed_product_count_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    (∑ z ∈ closedProductValues q (1 - 0.26213 / Real.log x) (x / q),
      analyticOrderNatAt (productL q) z) ≤ 4 := by
  rw [← closedFamilyCount_eq_product_count]
  exact closed_family_le_four hx hq hRS hgammaHigh hgammaLow

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap
