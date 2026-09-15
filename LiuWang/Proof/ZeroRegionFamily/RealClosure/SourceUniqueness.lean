import LiuWang.Proof.ZeroRegionFamily.RealClosure.Strong

/-! # 共同来源本身的存在唯一性，不仅是由两个普通字符取得的来源相等 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

theorem unique_datum_of_actual_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : region x q rho) (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃! d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧ datumL d rho=0 := by
  obtain ⟨hc, hcs, hi, _⟩ := zero_real_quadratic_simple hx hq chi hr hpole hz
  have hpos : 0 < rho.re := by linarith [region_re_half hx hr]
  have heq : (rho.re : ℂ)=rho := by apply Complex.ext <;> simp [hi]
  have hd : ((primitiveSource chi hc hcs).modulus : ℝ) ≤ x :=
    (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  have hdz := primitiveSource_zero chi hc hcs hpos hz
  refine ⟨primitiveSource chi hc hcs, ⟨hd, hdz⟩, ?_⟩
  intro e he
  exact real_sources_unique e _ hx he.1 hd hpos hpos
    (by simpa only [heq] using he.2) (by simpa only [heq] using hdz)
    (by linarith [hr.1]) (by linarith [hr.1])

theorem any_source_controls_family {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : region x q rho) (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0)
    (d : PrimitiveQuadraticDatum) (hd : (d.modulus : ℝ) ≤ x) (hdz : datumL d rho=0) :
    d.modulus=chi.conductor ∧ inducedAt d q=chi ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          region x r tau → (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
            tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨e, he, hec, hei, hez, _, _, hall⟩ := family_fixed_source hx hq chi hr hpole hz
  have hde := (unique_datum_of_actual_zero hx hq chi hr hpole hz).unique ⟨hd, hdz⟩ ⟨he, hez⟩
  subst e
  exact ⟨hec, hei, hall⟩

end LiuWang.Proof.ZeroRegionFamily.RealClosure
