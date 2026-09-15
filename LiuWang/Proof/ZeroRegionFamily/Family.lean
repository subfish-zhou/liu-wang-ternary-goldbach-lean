import LiuWang.Proof.ZeroRegionFamily.WeakRegion

/-! # 较窄区域内单模计重数至多一与全族共同实际本原来源 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily

theorem source_gap_of_weak {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : weakRegion x q rho) :
    1-rho.re < 1/(3*Real.log chi.conductor) := by
  have hlog := conductor_height_log_le hx hq chi hr.2
  have hL := log_scale_gt_one hx
  have hlogr := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hc)
  have htlog : 0 ≤ Real.log (|rho.im|+2) := Real.log_nonneg (by linarith [abs_nonneg rho.im])
  have hw : 1/(2560*Real.log x) ≤ 1/(3*Real.log chi.conductor) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  linarith [hr.1]

theorem weak_sources_equal {x : ℝ} {q r : ℕ} [NeZero q] [NeZero r]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (hr : (r : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi ≠ 1) (hp : psi ≠ 1) (hcs : chi^2=1) (hps : psi^2=1)
    {rho tau : ℂ} (hwr : weakRegion x q rho) (hwt : weakRegion x r tau)
    (hzr : chi.LFunction rho=0) (hzt : psi.LFunction tau=0)
    (hir : rho.im=0) (hit : tau.im=0) :
    primitiveSource chi hc hcs = primitiveSource psi hp hps := by
  have heqr : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hir]
  have heqt : (tau.re : ℂ) = tau := by apply Complex.ext <;> simp [hit]
  have hL := log_scale_gt_one hx
  have hw : 1/(2560*Real.log x) ≤ 1/(24*Real.log x) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  apply real_sources_unique _ _ hx
    ((show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq)
    ((show (psi.conductor : ℝ) ≤ r by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level psi).trans hr)
    (weakRegion_re_pos hx hwr) (weakRegion_re_pos hx hwt)
    (by simpa only [heqr] using primitiveSource_zero chi hc hcs (weakRegion_re_pos hx hwr) hzr)
    (by simpa only [heqt] using primitiveSource_zero psi hp hps (weakRegion_re_pos hx hwt) hzt)
    (by linarith [hwr.1]) (by linarith [hwt.1])

theorem weak_family_zero_equal {x : ℝ} {q r : ℕ} [NeZero q] [NeZero r]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (hr : (r : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    {rho tau : ℂ} (hwr : weakRegion x q rho) (hwt : weakRegion x r tau)
    (hpr : chi ≠ 1 ∨ rho ≠ 1) (hpt : psi ≠ 1 ∨ tau ≠ 1)
    (hzr : chi.LFunction rho=0) (hzt : psi.LFunction tau=0) :
    rho=tau ∧ ∃ d : PrimitiveQuadraticDatum,
      (d.modulus : ℝ) ≤ x ∧ d.modulus=chi.conductor ∧ d.modulus=psi.conductor ∧
      d.modulus ∣ q ∧ d.modulus ∣ r ∧
      inducedAt d q=chi ∧ inducedAt d r=psi ∧ datumL d rho=0 := by
  obtain ⟨hc, hcs, hir, _⟩ := weak_zero_real_quadratic_simple hx hq chi hwr hpr hzr
  obtain ⟨hp, hps, hit, _⟩ := weak_zero_real_quadratic_simple hx hr psi hwt hpt hzt
  have he := weak_sources_equal hx hq hr chi psi hc hp hcs hps hwr hwt hzr hzt hir hit
  have hdmod := congrArg PrimitiveQuadraticDatum.modulus he
  have hzr' := primitiveSource_zero chi hc hcs (weakRegion_re_pos hx hwr) hzr
  have hzt' := primitiveSource_zero psi hp hps (weakRegion_re_pos hx hwt) hzt
  rw [← he] at hzt'
  have hgr := source_gap_of_weak hx hq chi hc hwr
  have hgt := source_gap_of_weak hx hr psi hp hwt
  change chi.conductor=psi.conductor at hdmod
  rw [← hdmod] at hgt
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hrt := primitive_real_zeros_unique
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive (weakRegion_re_pos hx hwr) (weakRegion_re_pos hx hwt)
    hzr' hzt' hir hit hgr hgt
  refine ⟨hrt, primitiveSource chi hc hcs, ?_, rfl, hdmod, chi.conductor_dvd_level, ?_,
    inducedAt_primitiveSource chi hc hcs, ?_, hzr'⟩
  · exact (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  · change chi.conductor ∣ r
    rw [hdmod]
    exact psi.conductor_dvd_level
  · rw [he]
    exact inducedAt_primitiveSource psi hp hps

theorem weak_single_modulus_unique {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi psi : DirichletCharacter ℂ q) {rho tau : ℂ}
    (hwr : weakRegion x q rho) (hwt : weakRegion x q tau)
    (hpr : chi ≠ 1 ∨ rho ≠ 1) (hpt : psi ≠ 1 ∨ tau ≠ 1)
    (hzr : chi.LFunction rho=0) (hzt : psi.LFunction tau=0) :
    chi=psi ∧ rho=tau := by
  obtain ⟨he, d, _, _, _, _, _, hdc, hdp, _⟩ :=
    weak_family_zero_equal hx hq hq chi psi hwr hwt hpr hpt hzr hzt
  exact ⟨hdc.symm.trans hdp, he⟩

def countedZeros (x : ℝ) (q : ℕ) [NeZero q] :=
  Σ z : {z : DirichletCharacter ℂ q × ℂ //
    weakRegion x q z.2 ∧ (z.1 ≠ 1 ∨ z.2 ≠ 1) ∧ z.1.LFunction z.2=0},
      Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)

theorem countedZeros_subsingleton {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) : Subsingleton (countedZeros x q) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have he := weak_single_modulus_unique hx hq z.val.1 w.val.1
    z.property.1 w.property.1 z.property.2.1 w.property.2.1 z.property.2.2 w.property.2.2
  have hzw : z=w := Subtype.ext (Prod.ext he.1 he.2)
  subst w
  have hm := (weak_zero_real_quadratic_simple hx hq z.val.1 z.property.1
    z.property.2.1 z.property.2.2).2.2.2
  have hij : i=j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hm.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hm.le
    omega
  subst j
  rfl

theorem weak_family_fixed_source {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hwr : weakRegion x q rho)
    (hpr : chi ≠ 1 ∨ rho ≠ 1) (hzr : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          weakRegion x r tau → (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
            tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨hc, hcs, hir, horder⟩ := weak_zero_real_quadratic_simple hx hq chi hwr hpr hzr
  refine ⟨primitiveSource chi hc hcs, ?_, rfl, inducedAt_primitiveSource chi hc hcs,
    primitiveSource_zero chi hc hcs (weakRegion_re_pos hx hwr) hzr, hir, horder, ?_⟩
  · exact (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  · intro r _ hr psi tau hwt hpt hzt
    obtain ⟨hp, hps, hit, hto⟩ := weak_zero_real_quadratic_simple hx hr psi hwt hpt hzt
    have hsource := weak_sources_equal hx hq hr chi psi hc hp hcs hps hwr hwt hzr hzt hir hit
    have hzero := (weak_family_zero_equal hx hq hr chi psi hwr hwt hpr hpt hzr hzt).1
    refine ⟨hzero.symm, ?_, ?_, ?_, hto⟩
    · exact congrArg PrimitiveQuadraticDatum.modulus hsource
    · rw [hsource]
      exact psi.conductor_dvd_level
    · rw [hsource]
      exact inducedAt_primitiveSource psi hp hps

end LiuWang.Proof.ZeroRegionFamily
