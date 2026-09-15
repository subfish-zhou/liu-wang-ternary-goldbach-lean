import LiuWang.Proof.SmallConductorExpansion.Coverage

/-! # The paid finite coverage consumed by actual primitive sources and ordinary zeros -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SmallConductorExpansion

theorem primitive_source_le_thirtytwo_original_region (d : PrimitiveQuadraticDatum)
    (hd : d.modulus ≤ 32) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    datumL d (beta : ℂ) ≠ 0 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  exact quadratic_level_le_thirtytwo_original_region hd d.character d.ne_one d.square_eq_one hx hb

theorem original_real_zero_source_ge_thirtythree (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : datumL d (beta : ℂ) = 0) : 33 ≤ d.modulus := by
  by_contra h
  exact primitive_source_le_thirtytwo_original_region d (by omega) hx hb hz

theorem r24_re_in_original_real_region {x : ℝ} (hx : 10 ≤ x) {beta : ℝ}
    (hb : 1 - 1 / (24 * Real.log x) < beta) :
    1 - 1 / (9.645908801 * Real.log x) ≤ beta := by
  have hlog := Sharp.log_scale_ge hx
  have hw : 1 / (24 * Real.log x) ≤ 1 / (9.645908801 * Real.log x) :=
    one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  linarith

theorem family_twentyfour_conductor_ge_thirtythree
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho = 0) :
    ∃ d : PrimitiveQuadraticDatum, 33 ≤ d.modulus ∧ (d.modulus : ℝ) ≤ x ∧
      d.modulus = chi.conductor ∧ inducedAt d q = chi ∧ datumL d rho = 0 ∧
      rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1 - 1 / (24 * Real.log x) < tau.re → |tau.im| ≤ x / (r : ℝ) →
          (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau = 0 →
            tau = rho ∧ d.modulus = psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r = psi ∧ analyticOrderNatAt psi.LFunction tau = 1 := by
  obtain ⟨d, hd, hdc, hdi, hdz, hi, ho, hall⟩ :=
    RealClosure.family_twentyfour_from_actual_zero hx hq chi rho hr ht hp hz
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hbound := original_real_zero_source_ge_thirtythree d hx
    (r24_re_in_original_real_region hx hr) (by simpa only [he] using hdz)
  exact ⟨d, hbound, hd, hdc, hdi, hdz, hi, ho, hall⟩

theorem ordinary_conductor_le_thirtytwo_ne_zero
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (hc : chi.conductor ≤ 32) {rho : ℂ}
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  intro hz
  obtain ⟨d, hd, _, hdc, _⟩ :=
    family_twentyfour_conductor_ge_thirtythree hx hq chi rho hr ht hp hz
  omega

end LiuWang.Proof.SmallConductorExpansion
