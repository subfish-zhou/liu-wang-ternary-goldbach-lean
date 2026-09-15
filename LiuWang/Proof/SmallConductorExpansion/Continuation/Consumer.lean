import LiuWang.Proof.SmallConductorExpansion.Continuation.Coverage

/-!
# Genuine exceptional sources consume the expanded finite coverage

The original real interval is used for the L-value exclusion. The complex
ordinary-L consumer retains the frozen R24 region, multiplicity, conductor,
induced character, and common-source conclusions without strengthening R24.
-/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

theorem primitive_paid_source_original_region (d : PrimitiveQuadraticDatum)
    (hd : PaidLevel d.modulus) {x beta : ℝ}
    (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    datumL d (beta : ℂ) ≠ 0 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  exact paid_level_original_region hd d.character d.ne_one d.square_eq_one hx hdx hb

theorem original_real_zero_source_unpaid (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : datumL d (beta : ℂ) = 0) :
    41 ≤ d.modulus ∧ d.modulus ≠ 43 ∧ d.modulus ≠ 67 ∧ d.modulus ≠ 163 := by
  have hn : ¬PaidLevel d.modulus := fun hd =>
    primitive_paid_source_original_region d hd hx hdx hb hz
  unfold PaidLevel at hn
  omega

theorem family_twentyfour_conductor_unpaid
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho = 0) :
    ∃ d : PrimitiveQuadraticDatum,
      (41 ≤ d.modulus ∧ d.modulus ≠ 43 ∧ d.modulus ≠ 67 ∧ d.modulus ≠ 163) ∧
      (d.modulus : ℝ) ≤ x ∧ d.modulus = chi.conductor ∧ inducedAt d q = chi ∧
      datumL d rho = 0 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1 - 1 / (24 * Real.log x) < tau.re → |tau.im| ≤ x / (r : ℝ) →
          (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau = 0 →
            tau = rho ∧ d.modulus = psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r = psi ∧ analyticOrderNatAt psi.LFunction tau = 1 := by
  obtain ⟨d, hd, hdc, hdi, hdz, hi, ho, hall⟩ :=
    RealClosure.family_twentyfour_from_actual_zero hx hq chi rho hr ht hp hz
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hbound := original_real_zero_source_unpaid d hx hd
    (r24_re_in_original_real_region hx hr) (by simpa only [he] using hdz)
  exact ⟨d, hbound, hd, hdc, hdi, hdz, hi, ho, hall⟩

theorem ordinary_paid_conductor_ne_zero
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (hc : PaidLevel chi.conductor) {rho : ℂ}
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  intro hz
  obtain ⟨d, hd, _, hdc, _⟩ :=
    family_twentyfour_conductor_unpaid hx hq chi rho hr ht hp hz
  rw [← hdc] at hc
  unfold PaidLevel at hc
  omega

end LiuWang.Proof.SmallConductorExpansion.Continuation
