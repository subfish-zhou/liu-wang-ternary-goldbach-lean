import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Strong

/-! # 原普通L字面闭窗：完整R14/160与较强独立分支 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem single_modulus_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) :
    Subsingleton (countedZeros x q) ∧
      ∀ (chi : DirichletCharacter ℂ q) (rho : ℂ),
        1-1/(14*Real.log x) < rho.re → |rho.im| ≤ x/(q : ℝ) →
          (chi ≠ 1 ∨ rho ≠ 1) → chi.LFunction rho=0 →
            chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  ⟨countedZeros_subsingleton hx hq,
    fun chi _ hr ht hp hz => zero_real_quadratic_simple hx hq chi ⟨hr, ht⟩ hp hz⟩

theorem family_fourteen_from_actual_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(14*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(14*Real.log x) < tau.re → |tau.im| ≤ x/(r : ℝ) →
            (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
              tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
                inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, hd, hc, hi, hdz, hir, hm, hall⟩ := family_fixed_source hx hq chi ⟨hr, ht⟩ hpole hz
  exact ⟨d, hd, hc, hi, hdz, hir, hm,
    fun r _ hq psi tau hr ht => hall r hq psi tau ⟨hr, ht⟩⟩

theorem any_source_controls_family {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
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

theorem requested_domain_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  zero_real_quadratic_simple (by linarith) hq chi ⟨hr, ht⟩ hpole hz

theorem modulus_one_fourteen {x : ℝ} (hx : 160 ≤ Real.log x) {rho : ℂ}
    (hr : 1-1/(14*Real.log x) < rho.re) (ht : |rho.im| ≤ x) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ 1).LFunction rho ≠ 0 :=
  principal_no_zero_fourteen hx hr (by simpa using ht) hpole

theorem modulus_one_ten {x : ℝ} (hx : 400 ≤ Real.log x) {rho : ℂ}
    (hr : 1-1/(10*Real.log x) < rho.re) (ht : |rho.im| ≤ x) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ 1).LFunction rho ≠ 0 :=
  principal_no_zero_ten hx hr (by simpa using ht) hpole

theorem real_source_controls_twelve {x : ℝ} (hx : 10 ≤ Real.log x)
    (d : PrimitiveQuadraticDatum) (hd : (d.modulus : ℝ) ≤ x) {beta : ℝ}
    (hb : 0 < beta) (hz : datumL d (beta : ℂ)=0) (hg : 1-beta < 1/(12*Real.log x)) :
    ∀ (e : PrimitiveQuadraticDatum) (gamma : ℝ), (e.modulus : ℝ) ≤ x →
      0 < gamma → datumL e (gamma : ℂ)=0 → 1-gamma < 1/(12*Real.log x) → e=d := by
  intro e gamma he hb' hz' hg'
  exact real_sources_unique_twelve e d hx he hd hb' hb hz' hz hg' hg

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
