import LiuWang.Proof.ZeroRegionFamily.Uniform.LowOrder

/-! # 普通L字面闭高度消费者；R20全族与更强已付分支分开 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

theorem single_modulus_twenty {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) :
    Subsingleton (countedZeros x q) ∧
      ∀ (chi : DirichletCharacter ℂ q) (rho : ℂ),
        1-1/(20*Real.log x) < rho.re → |rho.im| ≤ x/(q : ℝ) →
          (chi ≠ 1 ∨ rho ≠ 1) → chi.LFunction rho=0 →
            chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  ⟨countedZeros_subsingleton hx hq,
    fun chi _ hr ht hp hz => zero_real_quadratic_simple hx hq chi ⟨hr, ht⟩ hp hz⟩

theorem family_twenty_from_actual_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(20*Real.log x) < tau.re → |tau.im| ≤ x/(r : ℝ) →
            (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
              tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
                inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, hd, hc, hi, hdz, hir, hm, hall⟩ := family_fixed_source hx hq chi ⟨hr, ht⟩ hpole hz
  exact ⟨d, hd, hc, hi, hdz, hir, hm,
    fun r _ hq psi tau hr ht => hall r hq psi tau ⟨hr, ht⟩⟩

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

theorem residual_low_order_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hz : chi.LFunction rho=0) :
    (chi^2=1 ∨ chi^3=1) ∧ |rho.im| < 1/2 := by
  constructor
  · by_contra h
    push Not at h
    exact powers_two_three_no_zero_fourteen hx hq chi hc h.1 h.2 hr ht hz
  · by_contra h
    have hw : 1/(14*Real.log x) ≤ 1/(10*Real.log x) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    exact all_nonprincipal_high_no_zero_ten hx hq chi hc (by linarith) ht (le_of_not_gt h) hz

theorem principal_no_zero {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hpole : rho ≠ 1) : (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 :=
  RealClosure.principal_no_zero_twenty hx hr ht hpole

theorem modulus_one_no_zero {x : ℝ} (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ 1).LFunction rho ≠ 0 :=
  principal_no_zero hx hr (by simpa using ht) hpole

end LiuWang.Proof.ZeroRegionFamily.Uniform
