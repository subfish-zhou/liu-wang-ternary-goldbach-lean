import LiuWang.Proof.Campaign20260915.GammaLow.Consumers
import LiuWang.Proof.Campaign20260915.GammaHigh.Consumers

/-!
Parent integration of the independently checked low/high Gamma producers.
The original zero-count consumers below retain only the separate finite-height
zeta premise. This is not a proof of that premise or of ternary Goldbach.
-/

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

namespace LiuWang.Proof.Campaign20260915.Parent

theorem original_T1_strict_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) :
    strictFamilyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 :=
  GammaLow.original_T1_strict_family_le_four hx hq hRS
    (GammaHigh.source_gammaHalfDifference_high hx)

theorem original_T1_product_count_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) :
    (∑ z ∈ productZeroValues q (1 - 0.26213 / Real.log x) (x / q),
      analyticOrderNatAt (productL q) z) ≤ 4 :=
  GammaLow.original_T1_product_count_le_four hx hq hRS
    (GammaHigh.source_gammaHalfDifference_high hx)

theorem original_T1_slot_card_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) :
    Fintype.card (ZeroSlots q (1 - 0.26213 / Real.log x) (x / q)) ≤ 4 :=
  GammaLow.original_T1_slot_card_le_four hx hq hRS
    (GammaHigh.source_gammaHalfDifference_high hx)

theorem closed_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) :
    familyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 :=
  GammaLow.closed_family_le_four hx hq hRS
    (GammaHigh.source_gammaHalfDifference_high hx)

theorem closed_slot_card_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) :
    Fintype.card (ClosedSlots q (1 - 0.26213 / Real.log x) (x / q)) ≤ 4 :=
  GammaLow.closed_slot_card_le_four hx hq hRS
    (GammaHigh.source_gammaHalfDifference_high hx)

theorem closed_product_count_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) :
    (∑ z ∈ closedProductValues q (1 - 0.26213 / Real.log x) (x / q),
      analyticOrderNatAt (productL q) z) ≤ 4 :=
  GammaLow.closed_product_count_le_four hx hq hRS
    (GammaHigh.source_gammaHalfDifference_high hx)

theorem lwd_case_ii {d q : ℕ} [NeZero d] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {rho tau upsilon : ℂ}
    (h : CaseIIData x q chi rho tau upsilon) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi
      (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 0.3284 :=
  GammaLow.lwd_case_ii h
    (fun t ht => (GammaHigh.source_gammaHalfDifference_high h.scale_ge t ht).le)

#check @original_T1_strict_family_le_four
#check @original_T1_product_count_le_four
#check @original_T1_slot_card_le_four
#check @closed_family_le_four
#check @closed_slot_card_le_four
#check @closed_product_count_le_four
#check @lwd_case_ii
#print axioms original_T1_strict_family_le_four
#print axioms original_T1_product_count_le_four
#print axioms original_T1_slot_card_le_four
#print axioms closed_family_le_four
#print axioms closed_slot_card_le_four
#print axioms closed_product_count_le_four
#print axioms lwd_case_ii

end LiuWang.Proof.Campaign20260915.Parent
