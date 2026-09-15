import LiuWang.Proof.SourceRoute.MajorException.Continuation.HeadPrecision

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

def paidArithmeticFactor (d : ℕ) : PureKind → ℝ
  | .linear => (moebiusWeight d*Real.sqrt d/(d.totient : ℝ)^2) * 2.826575
  | .quadratic => (moebiusWeight d*(d : ℝ)/(d.totient : ℝ)^2) * 2.826575
  | .cubic => ((d : ℝ)*Real.sqrt d/(d.totient : ℝ)^2) * 3.390828

theorem reducedArithmeticFactor_paid (X d : ℕ) (j : PureKind) :
    reducedArithmeticFactor X d j ≤ paidArithmeticFactor d j := by
  cases j with
  | linear =>
    exact mul_le_mul_of_nonneg_left (squarefreeTotientMass_stronger (X/d))
      (by dsimp [moebiusWeight]; positivity)
  | quadratic =>
    exact mul_le_mul_of_nonneg_left (squarefreeTotientMass_stronger (X/d))
      (by dsimp [moebiusWeight]; positivity)
  | cubic =>
    exact mul_le_mul_of_nonneg_left (totientMass_stronger (X/d)) (by positivity)

theorem sourceArithmetic_paid (X : ℕ) {d : ℕ} (hd : 0 < d) (j : PureKind) :
    (∑ q ∈ Finset.Icc 1 X, if d ∣ q then sourceArithmeticFactor q d j else 0) ≤
      paidArithmeticFactor d j :=
  (sourceArithmetic_reduction X hd j).trans (reducedArithmeticFactor_paid X d j)

theorem fixed_source_pure_totals_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      ∀ j : PureKind,
        (∑ s ∈ denominators (sourceP N), ‖selectedPureArc N s j‖) ≤
          sourceMomentFactor N rho.re j * paidArithmeticFactor d.modulus j := by
  obtain ⟨d, hd, hall⟩ := fixed_source_pure_totals hN hq hr
  exact ⟨d, hd, fun j => (hall j).trans
    (mul_le_mul_of_nonneg_left (reducedArithmeticFactor_paid _ _ j)
      (sourceMomentFactor_nonneg _ _ j))⟩

theorem fixed_source_pure_integrals_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      ∀ j : PureKind, ‖selectedPureIntegral N j‖ ≤
        sourceMomentFactor N rho.re j * paidArithmeticFactor d.modulus j := by
  obtain ⟨d, hd, hall⟩ := fixed_source_pure_totals_paid hN hq hr
  exact ⟨d, hd, fun j => (norm_sum_le _ _).trans (hall j)⟩

end LiuWang.Proof.SourceRoute.MajorException.Continuation
