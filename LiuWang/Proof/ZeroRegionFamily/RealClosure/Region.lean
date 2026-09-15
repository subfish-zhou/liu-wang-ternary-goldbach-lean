import LiuWang.Proof.ZeroRegionFamily.RealClosure.Principal

/-! # R24全部普通字符实际实、二次、单零点；极点显式不计 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

def region (x : ℝ) (q : ℕ) (rho : ℂ) : Prop :=
  1-1/(24*Real.log x) < rho.re ∧ |rho.im| ≤ x/(q : ℝ)

theorem region_re_half {x : ℝ} {q : ℕ} {rho : ℂ}
    (hx : 10 ≤ x) (hr : region x q rho) : 1/2 < rho.re := by
  have hL := log_scale_ge hx
  have hw : 1/(24*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  linarith [hr.1]

theorem region_to_twenty {x : ℝ} {q : ℕ} {rho : ℂ}
    (hx : 10 ≤ x) (hr : region x q rho) : 1-1/(20*Real.log x) < rho.re := by
  have hL := log_scale_ge hx
  have hw : 1/(24*Real.log x) ≤ 1/(20*Real.log x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith [hr.1]

theorem region_source_gap {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x)
    (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : region x q rho) : 1-rho.re < 1/(3*Real.log chi.conductor) := by
  have hL := log_scale_ge hx
  have hl := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hc)
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hlog := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero) (hcq.trans hq)
  have hw : 1/(24*Real.log x) ≤ 1/(3*Real.log chi.conductor) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith [hr.1]

theorem nonprincipal_zero_real {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : region x q rho) (hz : chi.LFunction rho=0) : chi^2=1 ∧ rho.im=0 := by
  have hloc := ordinary_zero_localized_twenty hx hq chi hc (region_to_twenty hx hr) hr.2 hz
  refine ⟨hloc.1, ?_⟩
  by_contra hi
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hc0 : (0 : ℝ) < chi.conductor := by exact_mod_cast NeZero.pos chi.conductor
  have ht : |rho.im| ≤ x/(chi.conductor : ℝ) :=
    hr.2.trans (div_le_div_of_nonneg_left (by linarith) hc0 hcq)
  have hh := primitive_quadratic_nonreal_gap_twentyfour hx (hcq.trans hq)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi hloc.1)
    (region_re_half hx hr)
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc
      (by linarith [region_re_half hx hr]) hz) hi ht
  linarith [hr.1]

theorem zero_real_quadratic_simple {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : region x q rho) (hpole : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    exact principal_no_zero_twenty hx (region_to_twenty hx hr) hr.2
      (hpole.resolve_left (by simp)) hz
  obtain ⟨hsq, hi⟩ := nonprincipal_zero_real hx hq chi hc hr hz
  exact ⟨hc, hsq, hi, real_zero_simple hc (by linarith [region_re_half hx hr])
    hz hi (region_source_gap hx hq chi hc hr)⟩

end LiuWang.Proof.ZeroRegionFamily.RealClosure
