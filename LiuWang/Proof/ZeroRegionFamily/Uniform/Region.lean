import LiuWang.Proof.ZeroRegionFamily.Uniform.RealRepulsion

/-! # 全部普通字符的R20实、二次、单零点区域 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

def region (x : ℝ) (q : ℕ) (rho : ℂ) : Prop :=
  1-1/(20*Real.log x) < rho.re ∧ |rho.im| ≤ x/(q : ℝ)

theorem region_re_half {x : ℝ} {q : ℕ} {rho : ℂ}
    (hx : 10 ≤ x) (hr : region x q rho) : 1/2 < rho.re := by
  have hL := log_scale_ge hx
  have hw : 1/(20*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
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
  have hw : 1/(20*Real.log x) ≤ 1/(3*Real.log chi.conductor) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith [hr.1]

theorem region_source_sixteen {x : ℝ} {q : ℕ} {rho : ℂ}
    (hx : 10 ≤ x) (hr : region x q rho) : 1-rho.re < 1/(16*Real.log x) := by
  have hL := log_scale_ge hx
  have hw : 1/(20*Real.log x) ≤ 1/(16*Real.log x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith [hr.1]

theorem zero_real_quadratic_simple {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : region x q rho) (hpole : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    exact RealClosure.principal_no_zero_twenty hx hr.1 hr.2
      (hpole.resolve_left (by simp)) hz
  obtain ⟨hsq, hi⟩ := ordinary_zero_real_twenty hx hq chi hc hr.1 hr.2 hz
  exact ⟨hc, hsq, hi, real_zero_simple hc (by linarith [region_re_half hx hr])
    hz hi (region_source_gap hx hq chi hc hr)⟩

end LiuWang.Proof.ZeroRegionFamily.Uniform
