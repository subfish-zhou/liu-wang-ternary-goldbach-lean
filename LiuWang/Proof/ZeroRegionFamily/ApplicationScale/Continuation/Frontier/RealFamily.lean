import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.Quartic

/-! # R8的真实实二次零点层：普通L、解析阶及一次固定来源

本文件仅处理实二次字符的实零点，不声称原R区域内所有零点均属此层。
-/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

theorem real_region_positive {x beta : ℝ} (hx : 10 ≤ x)
    (hgap : 1-beta < 1/(8*Real.log x)) : 0 < beta := by
  have hlog := log_scale_ge_34_15 hx
  have hw : 1/(8*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  linarith

theorem real_region_conductor_gap {x : ℝ} {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {beta : ℝ} (hgap : 1-beta < 1/(8*Real.log x)) :
    1-beta < 1/(3*Real.log chi.conductor) := by
  have hl := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hc)
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hlog := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero) (hcq.trans hq)
  have hw : 1/(8*Real.log x) ≤ 1/(3*Real.log chi.conductor) := by
    apply one_div_le_one_div_of_le (by linarith)
    linarith
  exact hgap.trans_le hw

theorem ordinary_real_zero_simple_eight {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {beta : ℝ} (hgap : 1-beta < 1/(8*Real.log x)) (hz : chi.LFunction (beta : ℂ)=0) :
    analyticOrderNatAt chi.LFunction (beta : ℂ)=1 := by
  exact real_zero_simple hc (by simpa only [Complex.ofReal_re] using real_region_positive hx hgap)
    hz (by simp) (by simpa only [Complex.ofReal_re] using real_region_conductor_gap hq chi hc hgap)

theorem real_family_fixed_source_eight {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hcs : chi^2=1) {beta : ℝ}
    (hgap : 1-beta < 1/(8*Real.log x)) (hz : chi.LFunction (beta : ℂ)=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ d.modulus ∣ q ∧ inducedAt d q=chi ∧ datumL d (beta : ℂ)=0 ∧
      analyticOrderNatAt chi.LFunction (beta : ℂ)=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (gamma : ℝ),
          psi ≠ 1 → psi^2=1 → 1-gamma < 1/(8*Real.log x) → psi.LFunction (gamma : ℂ)=0 →
            gamma=beta ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧ inducedAt d r=psi ∧
              analyticOrderNatAt psi.LFunction (gamma : ℂ)=1 := by
  have hb := real_region_positive hx hgap
  have hd : ((primitiveSource chi hc hcs).modulus : ℝ) ≤ x :=
    (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  have hzb := primitiveSource_zero chi hc hcs (by simpa only [Complex.ofReal_re] using hb) hz
  refine ⟨primitiveSource chi hc hcs, hd, rfl, chi.conductor_dvd_level,
    inducedAt_primitiveSource chi hc hcs, hzb, ordinary_real_zero_simple_eight hx hq chi hc hgap hz, ?_⟩
  intro r _ hr psi gamma hp hps hgg hzg
  have hg := real_region_positive hx hgg
  have hzg' := primitiveSource_zero psi hp hps (by simpa only [Complex.ofReal_re] using hg) hzg
  have he : primitiveSource chi hc hcs=primitiveSource psi hp hps :=
    real_sources_unique_eight _ _ hx hd
      ((show (psi.conductor : ℝ) ≤ r by
        exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level psi).trans hr)
      hzb hzg' hgap hgg
  have hmod := congrArg PrimitiveQuadraticDatum.modulus he
  have hzero : gamma=beta := by
    rw [← he] at hzg'
    have hgg' := real_region_conductor_gap hr psi hp hgg
    change chi.conductor=psi.conductor at hmod
    rw [← hmod] at hgg'
    let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hh := primitive_real_zeros_unique
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
      chi.primitiveCharacter_isPrimitive (by simpa only [Complex.ofReal_re] using hb)
      (by simpa only [Complex.ofReal_re] using hg) hzb hzg' (by simp) (by simp)
      (real_region_conductor_gap hq chi hc hgap) hgg'
    exact (Complex.ofReal_injective hh).symm
  refine ⟨hzero, hmod, ?_, ?_, ordinary_real_zero_simple_eight hx hr psi hp hgg hzg⟩
  · rw [he]
    exact psi.conductor_dvd_level
  · rw [he]
    exact inducedAt_primitiveSource psi hp hps

def countedRealQuadraticZeros (x : ℝ) (q : ℕ) [NeZero q] :=
  Σ z : {z : DirichletCharacter ℂ q × ℝ //
    z.1 ≠ 1 ∧ z.1^2=1 ∧ 1-z.2 < 1/(8*Real.log x) ∧ z.1.LFunction (z.2 : ℂ)=0},
      Fin (analyticOrderNatAt z.val.1.LFunction (z.val.2 : ℂ))

theorem countedRealQuadraticZeros_subsingleton {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) : Subsingleton (countedRealQuadraticZeros x q) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  obtain ⟨d, _, _, _, hi, _, hm, hall⟩ := real_family_fixed_source_eight hx hq z.val.1
    z.property.1 z.property.2.1 z.property.2.2.1 z.property.2.2.2
  obtain ⟨he, _, _, hi', _⟩ := hall q hq w.val.1 w.val.2 w.property.1 w.property.2.1
    w.property.2.2.1 w.property.2.2.2
  have hzw : z=w := Subtype.ext (Prod.ext (hi.symm.trans hi') he.symm)
  subst w
  have hij : i=j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hm.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hm.le
    omega
  subst j
  rfl

theorem real_family_fixed_source_original {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hcs : chi^2=1) {beta : ℝ}
    (hgap : 1-beta < 1/(9.645908801*Real.log x)) (hz : chi.LFunction (beta : ℂ)=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ d.modulus ∣ q ∧ inducedAt d q=chi ∧ datumL d (beta : ℂ)=0 ∧
      analyticOrderNatAt chi.LFunction (beta : ℂ)=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (gamma : ℝ),
          psi ≠ 1 → psi^2=1 → 1-gamma < 1/(9.645908801*Real.log x) → psi.LFunction (gamma : ℂ)=0 →
            gamma=beta ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧ inducedAt d r=psi ∧
              analyticOrderNatAt psi.LFunction (gamma : ℂ)=1 := by
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hw : 1/(9.645908801*Real.log x) ≤ 1/(8*Real.log x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨d, hd, hdc, hdq, hi, hdz, hm, hall⟩ :=
    real_family_fixed_source_eight hx hq chi hc hcs (hgap.trans_le hw) hz
  refine ⟨d, hd, hdc, hdq, hi, hdz, hm, ?_⟩
  intro r _ hr psi gamma hp hps hg hzg
  exact hall r hr psi gamma hp hps (hg.trans_le hw) hzg

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
