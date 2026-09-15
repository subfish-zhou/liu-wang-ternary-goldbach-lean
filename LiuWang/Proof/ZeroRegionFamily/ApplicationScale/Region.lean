import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Principal

/-! # 原R14闭高度窗口，不另造零点对象 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.LowOrderClosure (region countedZeros)

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale

theorem region_re_half {x : ℝ} {q : ℕ} {rho : ℂ}
    (hx : 20 ≤ Real.log x) (hr : region x q rho) : 1/2 < rho.re := by
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  linarith [hr.1]

theorem region_source_gap {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 20 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : region x q rho) :
    1-rho.re < 1/(3*Real.log chi.conductor) := by
  have hl := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hc)
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hlog := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero) (hcq.trans hq)
  have hw : 1/(14*Real.log x) ≤ 1/(3*Real.log chi.conductor) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith [hr.1]

theorem zero_real_quadratic_simple {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 20 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : region x q rho) (hpole : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    exact principal_no_zero_fourteen (by linarith) hr.1 hr.2
      (hpole.resolve_left (by simp)) hz
  obtain ⟨hsq, hi⟩ := ordinary_zero_real hx hq chi hc hr.1 hr.2 hz
  exact ⟨hc, hsq, hi, real_zero_simple hc (by linarith [region_re_half hx hr])
    hz hi (region_source_gap hx hq chi hc hr)⟩

theorem scale_ten_of_level {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 20 ≤ Real.log x) (hq : (q : ℝ) ≤ x) : 10 ≤ x := by
  have hp : 0 < x := (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q).trans_le hq
  by_contra h
  have hh := Real.log_le_log hp (le_of_not_ge h)
  have h10 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
  linarith

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale
