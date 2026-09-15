import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Windows
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Cases

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

theorem strict_count_to_2_28 {q : ℕ} [NeZero q] {x alpha : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (ha : 1 / 2 ≤ alpha) (hg : 1 - alpha ≤ lwdSourceSigma x - 1)
    (hcount : 4 < strictFamilyCount q alpha (x / q))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    ∃ p r u : ZeroSlots q alpha (x / q),
      CountedData x q alpha p.character.primitiveCharacter r.character.primitiveCharacter
        u.character.primitiveCharacter p r u ∧
      0 ≤ 1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - p.value.re) + 1 / (lwdSourceSigma x - r.value.re) +
          1 / (lwdSourceSigma x - u.value.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  obtain ⟨p, r, u, hsep⟩ := general_five_slots_extract_three hcount
  have hdom (v : ZeroSlots q alpha (x / q)) :
      1 / 2 < v.value.re ∧ 1 - v.value.re ≤ lwdSourceSigma x - 1 := by
    have hv := (mem_strictZeroValues.mp v.zero_mem).2.2.1
    constructor <;> linarith
  have h := canonical_counted_data hx hq p r u
    ⟨(hdom p).1, (hdom r).1, (hdom u).1⟩ ⟨(hdom p).2, (hdom r).2, (hdom u).2⟩ hsep
  exact ⟨p, r, u, h, counted_eight_case_2_28 h hRS hgammaHigh hgammaLow⟩

theorem closed_count_to_2_28 {q : ℕ} [NeZero q] {x alpha : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (ha : 1 / 2 < alpha) (hg : 1 - alpha ≤ lwdSourceSigma x - 1)
    (hcount : 4 < familyCount q alpha (x / q))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    ∃ p r u : ClosedSlots q alpha (x / q),
      CountedData x q 0 p.val.character.primitiveCharacter r.val.character.primitiveCharacter
        u.val.character.primitiveCharacter p.val r.val u.val ∧
      0 ≤ 1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - p.val.value.re) + 1 / (lwdSourceSigma x - r.val.value.re) +
          1 / (lwdSourceSigma x - u.val.value.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  obtain ⟨p, r, u, hsep⟩ := closed_five_extract_three hcount
  have hdom (v : ClosedSlots q alpha (x / q)) :
      1 / 2 < v.val.value.re ∧ 1 - v.val.value.re ≤ lwdSourceSigma x - 1 := by
    have hv := v.property
    constructor <;> linarith
  have h := canonical_counted_data hx hq p.val r.val u.val
    ⟨(hdom p).1, (hdom r).1, (hdom u).1⟩ ⟨(hdom p).2, (hdom r).2, (hdom u).2⟩ hsep
  exact ⟨p, r, u, h, counted_eight_case_2_28 h hRS hgammaHigh hgammaLow⟩

theorem original_window_domain {x : ℝ} (hx : 8000000000 ≤ x) :
    1 / 2 < 1 - 0.26213 / Real.log x ∧
      1 - (1 - 0.26213 / Real.log x) ≤ lwdSourceSigma x - 1 := by
  have hL := source_log_twenty_two hx
  have hL0 : 0 < Real.log x := by linarith
  have hsqrt := Real.sqrt_nonneg 3
  have hsqrt2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hg : (2.4998 : ℝ) / Real.log x ≤ 0.114 := (div_le_iff₀ hL0).mpr (by linarith)
  have hden : 0 < 7 * stechkinConductorCoeff + 2.4998 / Real.log x := by
    have hk := lwd_kappa_bounds.1
    positivity
  have ha : 0.26213 ≤ lwdSourceA x := by
    unfold lwdSourceA
    apply (le_div_iff₀ hden).mpr
    have hs : (1.732 : ℝ) ≤ Real.sqrt 3 := by nlinarith
    nlinarith [lwd_kappa_bounds.2]
  have hsmall : (0.26213 : ℝ) / Real.log x < 1 / 2 :=
    (div_lt_iff₀ hL0).mpr (by linarith)
  refine ⟨by linarith, ?_⟩
  have hh := div_le_div_of_nonneg_right ha hL0.le
  unfold lwdSourceSigma
  linarith

theorem original_product_to_2_28 {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hcount : 4 < ∑ z ∈ productZeroValues q (1 - 0.26213 / Real.log x) (x / q),
      analyticOrderNatAt (productL q) z)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    ∃ p r u : ZeroSlots q (1 - 0.26213 / Real.log x) (x / q),
      CountedData x q (1 - 0.26213 / Real.log x) p.character.primitiveCharacter
        r.character.primitiveCharacter u.character.primitiveCharacter p r u ∧
      0 ≤ 1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - p.value.re) + 1 / (lwdSourceSigma x - r.value.re) +
          1 / (lwdSourceSigma x - u.value.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  rw [← strictFamilyCount_eq_product_count] at hcount
  exact strict_count_to_2_28 hx hq (original_window_domain hx).1.le
    (original_window_domain hx).2 hcount hRS hgammaHigh hgammaLow

theorem original_closed_family_to_2_28 {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hcount : 4 < familyCount q (1 - 0.26213 / Real.log x) (x / q))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    ∃ p r u : ClosedSlots q (1 - 0.26213 / Real.log x) (x / q),
      CountedData x q 0 p.val.character.primitiveCharacter r.val.character.primitiveCharacter
        u.val.character.primitiveCharacter p.val r.val u.val ∧
      0 ≤ 1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - p.val.value.re) + 1 / (lwdSourceSigma x - r.val.value.re) +
          1 / (lwdSourceSigma x - u.val.value.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 :=
  closed_count_to_2_28 hx hq (original_window_domain hx).1 (original_window_domain hx).2
    hcount hRS hgammaHigh hgammaLow

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
