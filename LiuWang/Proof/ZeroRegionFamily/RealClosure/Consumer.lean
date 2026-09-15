import LiuWang.Proof.ZeroRegionFamily.RealClosure.Family

/-! # 原普通L、字面闭高度、共同来源和普通解析阶的公共消费者 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

theorem single_modulus_twentyfour {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) :
    Subsingleton (countedZeros x q) ∧
    ∀ (chi : DirichletCharacter ℂ q) (rho : ℂ),
      1-1/(24*Real.log x) < rho.re → |rho.im| ≤ x/(q : ℝ) →
      (chi ≠ 1 ∨ rho ≠ 1) → chi.LFunction rho=0 →
        chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  ⟨countedZeros_subsingleton hx hq,
    fun chi _ hr ht hp hz => zero_real_quadratic_simple hx hq chi ⟨hr, ht⟩ hp hz⟩

theorem family_twentyfour_from_actual_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (hr : 1-1/(24*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(24*Real.log x) < tau.re → |tau.im| ≤ x/(r : ℝ) →
          (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
            tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, hd, hdc, hdi, hdz, hi, ho, hall⟩ :=
    family_fixed_source hx hq chi ⟨hr, ht⟩ hp hz
  exact ⟨d, hd, hdc, hdi, hdz, hi, ho,
    fun r _ hrx psi tau hr' ht' hp' hz' => hall r hrx psi tau ⟨hr', ht'⟩ hp' hz'⟩

theorem modulus_one_no_zero {x : ℝ} (hx : 10 ≤ x)
    (chi : DirichletCharacter ℂ 1) {rho : ℂ}
    (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x)
    (hpole : rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  have hc : chi=1 := Subsingleton.elim _ _
  subst chi
  exact principal_no_zero_twenty hx hr (by simpa using ht) hpole

theorem common_source_excludes_other_characters {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : region x q rho) (hp : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus=chi.conductor ∧ inducedAt d q=chi ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x → ∀ (psi : DirichletCharacter ℂ r),
        psi ≠ inducedAt d r → ∀ (tau : ℂ), region x r tau →
          (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau ≠ 0 := by
  obtain ⟨d, _, hdc, hdi, _, _, _, hall⟩ := family_fixed_source hx hq chi hr hp hz
  refine ⟨d, hdc, hdi, ?_⟩
  intro r _ hrx psi hne tau hrt hpt hzt
  exact hne (hall r hrx psi tau hrt hpt hzt).2.2.2.1.symm

end LiuWang.Proof.ZeroRegionFamily.RealClosure
