import LiuWang.Proof.Campaign20260915.GammaLow.LowSum
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.Counts

set_option autoImplicit false

noncomputable section

open Complex
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

namespace LiuWang.Proof.Campaign20260915.GammaLow

theorem original_T1_strict_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    strictFamilyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 :=
  CountCap.original_T1_strict_family_le_four hx hq hRS hgammaHigh (source_gamma_low hx)

theorem original_T1_product_count_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    (∑ z ∈ productZeroValues q (1 - 0.26213 / Real.log x) (x / q),
      analyticOrderNatAt (productL q) z) ≤ 4 :=
  CountCap.original_T1_product_count_le_four hx hq hRS hgammaHigh (source_gamma_low hx)

theorem original_T1_slot_card_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    Fintype.card (ZeroSlots q (1 - 0.26213 / Real.log x) (x / q)) ≤ 4 :=
  CountCap.original_T1_slot_card_le_four hx hq hRS hgammaHigh (source_gamma_low hx)

theorem closed_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    familyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 :=
  CountCap.closed_family_le_four hx hq hRS hgammaHigh (source_gamma_low hx)

theorem closed_slot_card_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    Fintype.card (ClosedSlots q (1 - 0.26213 / Real.log x) (x / q)) ≤ 4 :=
  CountCap.closed_slot_card_le_four hx hq hRS hgammaHigh (source_gamma_low hx)

theorem closed_product_count_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    (∑ z ∈ closedProductValues q (1 - 0.26213 / Real.log x) (x / q),
      analyticOrderNatAt (productL q) z) ≤ 4 :=
  CountCap.closed_product_count_le_four hx hq hRS hgammaHigh (source_gamma_low hx)

theorem lwd_case_ii {d q : ℕ} [NeZero d] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {rho tau upsilon : ℂ}
    (h : CaseIIData x q chi rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t ≤
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi
      (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 0.3284 :=
  PrincipalCases.lwd_case_ii h hgammaHigh
    (fun t ht => (source_gamma_low h.scale_ge t ht).le)

#print axioms original_T1_strict_family_le_four
#print axioms closed_family_le_four
#print axioms lwd_case_ii

end LiuWang.Proof.Campaign20260915.GammaLow
