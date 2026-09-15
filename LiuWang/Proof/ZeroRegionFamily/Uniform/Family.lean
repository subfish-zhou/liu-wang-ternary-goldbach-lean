import LiuWang.Proof.ZeroRegionFamily.Uniform.Region

/-! # R20单模计重数与固定的全族共同本原来源 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

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
  exact real_sources_unique_sixteen e _ hx he.1 hd hpos hpos
    (by simpa only [heq] using he.2) (by simpa only [heq] using hdz)
    (region_source_sixteen hx hr) (region_source_sixteen hx hr)

theorem sources_equal {x : ℝ} {q r : ℕ} [NeZero q] [NeZero r]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (hr : (r : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi ≠ 1) (hp : psi ≠ 1) (hcs : chi^2=1) (hps : psi^2=1)
    {rho tau : ℂ} (hwr : region x q rho) (hwt : region x r tau)
    (hzr : chi.LFunction rho=0) (hzt : psi.LFunction tau=0)
    (hir : rho.im=0) (hit : tau.im=0) :
    primitiveSource chi hc hcs = primitiveSource psi hp hps := by
  have heqr : (rho.re : ℂ)=rho := by apply Complex.ext <;> simp [hir]
  have heqt : (tau.re : ℂ)=tau := by apply Complex.ext <;> simp [hit]
  have hrr : 0 < rho.re := by linarith [region_re_half hx hwr]
  have hrt : 0 < tau.re := by linarith [region_re_half hx hwt]
  exact real_sources_unique_sixteen _ _ hx
    ((show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq)
    ((show (psi.conductor : ℝ) ≤ r by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level psi).trans hr)
    hrr hrt
    (by simpa only [heqr] using primitiveSource_zero chi hc hcs hrr hzr)
    (by simpa only [heqt] using primitiveSource_zero psi hp hps hrt hzt)
    (region_source_sixteen hx hwr) (region_source_sixteen hx hwt)

theorem family_zero_equal {x : ℝ} {q r : ℕ} [NeZero q] [NeZero r]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (hr : (r : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    {rho tau : ℂ} (hwr : region x q rho) (hwt : region x r tau)
    (hpr : chi ≠ 1 ∨ rho ≠ 1) (hpt : psi ≠ 1 ∨ tau ≠ 1)
    (hzr : chi.LFunction rho=0) (hzt : psi.LFunction tau=0) : rho=tau := by
  obtain ⟨hc, hcs, hir, _⟩ := zero_real_quadratic_simple hx hq chi hwr hpr hzr
  obtain ⟨hp, hps, hit, _⟩ := zero_real_quadratic_simple hx hr psi hwt hpt hzt
  have he := sources_equal hx hq hr chi psi hc hp hcs hps hwr hwt hzr hzt hir hit
  have hdmod := congrArg PrimitiveQuadraticDatum.modulus he
  have hrr : 0 < rho.re := by linarith [region_re_half hx hwr]
  have hrt : 0 < tau.re := by linarith [region_re_half hx hwt]
  have hzr' := primitiveSource_zero chi hc hcs hrr hzr
  have hzt' := primitiveSource_zero psi hp hps hrt hzt
  rw [← he] at hzt'
  have hgr := region_source_gap hx hq chi hc hwr
  have hgt := region_source_gap hx hr psi hp hwt
  change chi.conductor=psi.conductor at hdmod
  rw [← hdmod] at hgt
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact primitive_real_zeros_unique
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive hrr hrt hzr' hzt' hir hit hgr hgt

theorem single_modulus_unique {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi psi : DirichletCharacter ℂ q) {rho tau : ℂ}
    (hwr : region x q rho) (hwt : region x q tau)
    (hpr : chi ≠ 1 ∨ rho ≠ 1) (hpt : psi ≠ 1 ∨ tau ≠ 1)
    (hzr : chi.LFunction rho=0) (hzt : psi.LFunction tau=0) :
    chi=psi ∧ rho=tau := by
  obtain ⟨hc, hcs, hir, _⟩ := zero_real_quadratic_simple hx hq chi hwr hpr hzr
  obtain ⟨hp, hps, hit, _⟩ := zero_real_quadratic_simple hx hq psi hwt hpt hzt
  have he := congrArg (fun d => inducedAt d q)
    (sources_equal hx hq hq chi psi hc hp hcs hps hwr hwt hzr hzt hir hit)
  rw [inducedAt_primitiveSource, inducedAt_primitiveSource] at he
  exact ⟨he, family_zero_equal hx hq hq chi psi hwr hwt hpr hpt hzr hzt⟩

def countedZeros (x : ℝ) (q : ℕ) [NeZero q] :=
  Σ z : {z : DirichletCharacter ℂ q × ℂ //
    region x q z.2 ∧ (z.1 ≠ 1 ∨ z.2 ≠ 1) ∧ z.1.LFunction z.2=0},
      Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)

theorem countedZeros_subsingleton {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) : Subsingleton (countedZeros x q) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have he := single_modulus_unique hx hq z.val.1 w.val.1
    z.property.1 w.property.1 z.property.2.1 w.property.2.1 z.property.2.2 w.property.2.2
  have hzw : z=w := Subtype.ext (Prod.ext he.1 he.2)
  subst w
  have hm := (zero_real_quadratic_simple hx hq z.val.1 z.property.1
    z.property.2.1 z.property.2.2).2.2.2
  have hij : i=j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hm.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hm.le
    omega
  subst j
  rfl

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
  obtain ⟨hc, hcs, hir, horder⟩ := zero_real_quadratic_simple hx hq chi hwr hpr hzr
  refine ⟨primitiveSource chi hc hcs, ?_, rfl, inducedAt_primitiveSource chi hc hcs,
    primitiveSource_zero chi hc hcs (by linarith [region_re_half hx hwr]) hzr, hir, horder, ?_⟩
  · exact (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  · intro r _ hr psi tau hwt hpt hzt
    obtain ⟨hp, hps, hit, hto⟩ := zero_real_quadratic_simple hx hr psi hwt hpt hzt
    have hsource := sources_equal hx hq hr chi psi hc hp hcs hps hwr hwt hzr hzt hir hit
    refine ⟨(family_zero_equal hx hq hr chi psi hwr hwt hpr hpt hzr hzt).symm,
      congrArg PrimitiveQuadraticDatum.modulus hsource, ?_, ?_, hto⟩
    · rw [hsource]
      exact psi.conductor_dvd_level
    · rw [hsource]
      exact inducedAt_primitiveSource psi hp hps

end LiuWang.Proof.ZeroRegionFamily.Uniform
