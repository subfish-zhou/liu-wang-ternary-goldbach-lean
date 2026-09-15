import LiuWang.Proof.ZeroRegionFamily.PairRepulsion
import LiuWang.Proof.ChebyshevBound.HighHeight.QuarticZeroFree
import LiuWang.Proof.PrincipalPsi.EulerTransport

/-! # 已实际付款的较窄有限尺度区域，R=2560（不是McCurley原区域） -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily

def weakRegion (x : ℝ) (q : ℕ) (rho : ℂ) : Prop :=
  1-1/(2560*Real.log x) < rho.re ∧ |rho.im| ≤ x/(q : ℝ)

theorem log_scale_gt_one {x : ℝ} (hx : 10 ≤ x) : 1 < Real.log x := by
  apply (Real.lt_log_iff_exp_lt (by linarith)).mpr
  linarith [Real.exp_one_lt_d9]

theorem weakRegion_re_pos {x : ℝ} {q : ℕ} {rho : ℂ}
    (hx : 10 ≤ x) (hr : weakRegion x q rho) : 0 < rho.re := by
  have hL := log_scale_gt_one hx
  have hh : 1/(2560*Real.log x) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  linarith [hr.1]

theorem conductor_height_log_le {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {t : ℝ} (ht : |t| ≤ x/(q : ℝ)) :
    Real.log chi.conductor+Real.log (|t|+2) ≤ 2*Real.log x := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hr0 : (0 : ℝ) < chi.conductor := by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hrq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hheight := (le_div_iff₀ hq0).mp ht
  have hprod : (chi.conductor : ℝ)*(|t|+2) ≤ x^2 := by
    have hh := mul_le_mul_of_nonneg_right hrq (by positivity : 0 ≤ |t|+2)
    nlinarith
  rw [← Real.log_mul hr0.ne' (by positivity)]
  have hh := Real.log_le_log (by positivity : 0 < (chi.conductor : ℝ)*(|t|+2)) hprod
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

theorem principal_no_weak_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {rho : ℂ}
    (hr : weakRegion x q rho) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 := by
  have hpos := weakRegion_re_pos hx hr
  have hz := ChebyshevBound.HighHeight.zeta_zero_free_twenty (s := rho)
  have hL := log_scale_gt_one hx
  have hlog := conductor_height_log_le hx hq (1 : DirichletCharacter ℂ q) hr.2
  have hc : 0 ≤ Real.log (1 : DirichletCharacter ℂ q).conductor :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (1 : DirichletCharacter ℂ q).conductor_ne_zero))
  have hheight : 0 ≤ Real.log (|rho.im|+2) := Real.log_nonneg (by linarith [abs_nonneg rho.im])
  have hwidth : 1/(2560*Real.log x) ≤ 1/(20*(Real.log (|rho.im|+2)+2)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hn := hz (by linarith [hr.1])
  exact fun h => hn ((PrincipalPsi.principal_zero_iff_zeta_zero hpos hpole).mp h)

theorem weak_zero_real_quadratic_simple {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : weakRegion x q rho)
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho = 0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  have hchi : chi ≠ 1 := by
    intro he
    subst chi
    have hne : rho ≠ 1 := hpole.resolve_left (by simp)
    exact principal_no_weak_zero hx hq hr hne hz
  have hrpos := weakRegion_re_pos hx hr
  have hlog := conductor_height_log_le hx hq chi hr.2
  have hL := log_scale_gt_one hx
  have hlogr := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hchi)
  have htlog : 0 ≤ Real.log (|rho.im|+2) := Real.log_nonneg (by linarith [abs_nonneg rho.im])
  have hsq : chi^2=1 := by
    by_contra hh
    have hg := nonquadratic_gap hh hrpos hz
    have hw : 1/(2560*Real.log x) ≤
        1/(140*(Real.log chi.conductor+Real.log (|rho.im|+2))) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith [hr.1]
  have him : rho.im=0 := by
    by_contra hh
    have hg := quadratic_nonreal_gap hchi hsq hrpos hz hh
    have hw : 1/(2560*Real.log x) ≤
        1/(1280*(Real.log chi.conductor+Real.log (|rho.im|+2))) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith [hr.1]
  refine ⟨hchi, hsq, him, real_zero_simple hchi hrpos hz him ?_⟩
  have hw : 1/(2560*Real.log x) ≤ 1/(3*Real.log chi.conductor) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  linarith [hr.1]

def primitiveSource {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (hsq : chi^2=1) : PrimitiveQuadraticDatum :=
  ⟨chi.conductor, chi.conductor_ne_zero, chi.primitiveCharacter,
    chi.primitiveCharacter_isPrimitive,
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi hsq,
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi⟩

theorem primitiveSource_zero {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hsq : chi^2=1) {rho : ℂ}
    (hr : 0 < rho.re) (hz : chi.LFunction rho=0) :
    datumL (primitiveSource chi hc hsq) rho=0 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc hr hz

theorem primitiveSource_induces {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hsq : chi^2=1) :
    DirichletCharacter.changeLevel chi.conductor_dvd_level
      (primitiveSource chi hc hsq).character = chi :=
  chi.changeLevel_primitiveCharacter

def inducedAt (d : PrimitiveQuadraticDatum) (q : ℕ) : DirichletCharacter ℂ q :=
  if h : d.modulus ∣ q then DirichletCharacter.changeLevel h d.character else 1

theorem inducedAt_primitiveSource {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hsq : chi^2=1) :
    inducedAt (primitiveSource chi hc hsq) q = chi := by
  unfold inducedAt
  rw [dif_pos (show (primitiveSource chi hc hsq).modulus ∣ q from chi.conductor_dvd_level)]
  exact chi.changeLevel_primitiveCharacter

theorem primitiveSource_injective {q : ℕ} [NeZero q]
    {chi psi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : psi ≠ 1)
    (hcs : chi^2=1) (hps : psi^2=1)
    (he : primitiveSource chi hc hcs = primitiveSource psi hp hps) : chi=psi := by
  have hh := congrArg (fun d => inducedAt d q) he
  simpa only [inducedAt_primitiveSource] using hh

end LiuWang.Proof.ZeroRegionFamily
