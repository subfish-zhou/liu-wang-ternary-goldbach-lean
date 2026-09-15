import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Source

/-! # R40/3全域闭窗口，实际重数与一次固定的本原来源 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation

def region (x : ℝ) (q : ℕ) (rho : ℂ) : Prop :=
  1-3/(40*Real.log x) < rho.re ∧ |rho.im| ≤ x/(q : ℝ)

def countedZeros (x : ℝ) (q : ℕ) [NeZero q] :=
  Σ z : {z : DirichletCharacter ℂ q × ℂ //
    region x q z.2 ∧ (z.1 ≠ 1 ∨ z.2 ≠ 1) ∧ z.1.LFunction z.2=0},
      Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)

theorem unique_datum_of_actual_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : region x q rho) (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃! d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧ datumL d rho=0 := by
  obtain ⟨hc, hcs, hi, _⟩ := zero_real_quadratic_simple hx hq chi hr.1 hr.2 hpole hz
  have hpos : 0 < rho.re := by linarith [region_re_half hx hr.1]
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

theorem family_fixed_source {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hwr : region x q rho)
    (hpr : chi ≠ 1 ∨ rho ≠ 1) (hzr : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          region x r tau → (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
            tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨hc, hcs, hir, horder⟩ := zero_real_quadratic_simple hx hq chi hwr.1 hwr.2 hpr hzr
  have hrr : 0 < rho.re := by linarith [region_re_half hx hwr.1]
  have hd : ((primitiveSource chi hc hcs).modulus : ℝ) ≤ x :=
    (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  have hzr' := primitiveSource_zero chi hc hcs hrr hzr
  refine ⟨primitiveSource chi hc hcs, hd, rfl, inducedAt_primitiveSource chi hc hcs,
    hzr', hir, horder, ?_⟩
  intro r _ hr psi tau hwt hpt hzt
  obtain ⟨hp, hps, hit, hto⟩ := zero_real_quadratic_simple hx hr psi hwt.1 hwt.2 hpt hzt
  have hrt : 0 < tau.re := by linarith [region_re_half hx hwt.1]
  have heqr : (rho.re : ℂ)=rho := by apply Complex.ext <;> simp [hir]
  have heqt : (tau.re : ℂ)=tau := by apply Complex.ext <;> simp [hit]
  have hzt' := primitiveSource_zero psi hp hps hrt hzt
  have he : primitiveSource chi hc hcs=primitiveSource psi hp hps :=
    real_sources_unique _ _ hx hd
      ((show (psi.conductor : ℝ) ≤ r by
        exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level psi).trans hr)
      hrr hrt (by simpa only [heqr] using hzr') (by simpa only [heqt] using hzt')
      (by linarith [hwr.1]) (by linarith [hwt.1])
  have hdmod := congrArg PrimitiveQuadraticDatum.modulus he
  have hzero : tau=rho := by
    rw [← he] at hzt'
    have hgt := region_source_gap hr psi hp hwt.1
    change chi.conductor=psi.conductor at hdmod
    rw [← hdmod] at hgt
    let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    exact (primitive_real_zeros_unique
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
      chi.primitiveCharacter_isPrimitive hrr hrt hzr' hzt' hir hit
      (region_source_gap hq chi hc hwr.1) hgt).symm
  refine ⟨hzero, hdmod, ?_, ?_, hto⟩
  · rw [he]
    exact psi.conductor_dvd_level
  · rw [he]
    exact inducedAt_primitiveSource psi hp hps

theorem single_modulus_unique {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi psi : DirichletCharacter ℂ q) {rho tau : ℂ}
    (hwr : region x q rho) (hwt : region x q tau)
    (hpr : chi ≠ 1 ∨ rho ≠ 1) (hpt : psi ≠ 1 ∨ tau ≠ 1)
    (hzr : chi.LFunction rho=0) (hzt : psi.LFunction tau=0) :
    chi=psi ∧ rho=tau := by
  obtain ⟨d, _, _, hi, _, _, _, hall⟩ := family_fixed_source hx hq chi hwr hpr hzr
  obtain ⟨he, _, _, hi', _⟩ := hall q hq psi tau hwt hpt hzt
  exact ⟨hi.symm.trans hi', he.symm⟩

theorem countedZeros_subsingleton {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) : Subsingleton (countedZeros x q) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have he := single_modulus_unique hx hq z.val.1 w.val.1
    z.property.1 w.property.1 z.property.2.1 w.property.2.1 z.property.2.2 w.property.2.2
  have hzw : z=w := Subtype.ext (Prod.ext he.1 he.2)
  subst w
  have hm := (zero_real_quadratic_simple hx hq z.val.1 z.property.1.1 z.property.1.2
    z.property.2.1 z.property.2.2).2.2.2
  have hij : i=j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hm.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hm.le
    omega
  subst j
  rfl

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation
