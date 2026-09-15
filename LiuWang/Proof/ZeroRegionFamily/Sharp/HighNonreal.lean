import LiuWang.Proof.ZeroRegionFamily.Sharp.Nonquadratic

/-! # 真正主字符高线费用进入非实零点排除：闭|Im rho|>=1/2的R20分支 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem quadratic_high_core {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2=1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0) (ht : 1/2 ≤ |rho.im|)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    4/(sigma-rho.re) ≤ 3/(sigma-1)+
      5*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|)) := by
  have hpos := stechkin_combination_nonneg chi hs rho.im
  have hzero := primitive_actual_selected_bound hc hp hr hz hs hs1
  have hreal := principal_real_strong (q := q) hs hs1
  have hhigh := principal_high (q := q) hs hs1
    (t := 2*rho.im) (by rw [abs_mul]; norm_num; linarith)
  have hlog := log_max_double_le rho.im
  have ht2 : 1 ≤ |2*rho.im| := by rw [abs_mul]; norm_num; linarith
  rw [max_eq_right ht2] at hlog
  have hlog' := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  have hqlog := mul_nonneg conductorCoeff_bounds.1 (Real.log_natCast_nonneg q)
  have hconst : stechkinConductorCoeff*(Real.log 2-5*Real.log Real.pi) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos conductorCoeff_bounds.1
      (by linarith [Real.log_two_lt_d9, log_pi_ge_one])
  have hcost := principalPrimeCost_nonneg q hs
  have hk := stechkinK_mem.1
  rw [hsq] at hpos
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem finite_gap_of_log_core {x beta : ℝ} (hx : 10 ≤ x) (hb : beta < 1)
    (hcore : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 23/20 →
      4/(sigma-beta) ≤ 3/(sigma-1)+5*stechkinConductorCoeff*Real.log x) :
    1/(20*Real.log x) ≤ 1-beta := by
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  let u := 1/(3*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have huL : Real.log x*u=1/3 := by dsimp [u]; field_simp
  have hinv : 3/(1+u-1)=9*Real.log x := by dsimp [u]; field_simp; ring
  have hh := hcore (1+u) (by linarith) (by linarith)
  rw [hinv] at hh
  have h2 := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  have hupper : 4/(1+u-beta) ≤ (52/5)*Real.log x := by nlinarith
  have hden : 0 < 1+u-beta := by linarith
  have hpaid := (div_le_iff₀ hden).mp hupper
  by_contra h
  have hgap : (1-beta)*Real.log x < 1/20 := by
    have hg := (lt_div_iff₀ (show 0 < 20*Real.log x by positivity)).mp (lt_of_not_ge h)
    nlinarith
  nlinarith

theorem primitive_high_gap {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    (hlo : 1/2 ≤ |rho.im|) (ht : |rho.im| ≤ x/(q : ℝ)) :
    1/(20*Real.log x) ≤ 1-rho.re := by
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  apply finite_gap_of_log_core hx hb
  intro sigma hs hs1
  have hlog := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) conductorCoeff_bounds.1)
  by_cases hsq : chi^2=1
  · exact (quadratic_high_core hc hp hsq hr hz hlo hs hs1).trans
      (add_le_add le_rfl hlog)
  · exact (nonquadratic_core hc hp hsq hr hz hs hs1).trans (add_le_add le_rfl hlog)

theorem nonprincipal_high_no_zero_twenty {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : 1-1/(20*Real.log x) < rho.re)
    (hlo : 1/2 ≤ |rho.im|) (ht : |rho.im| ≤ x/(q : ℝ)) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL := log_scale_ge hx
  have hw : 1/(20*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hrhalf : 1/2 < rho.re := by linarith
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hrd : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hr0 : (0 : ℝ) < chi.conductor := by exact_mod_cast NeZero.pos chi.conductor
  have hheight : |rho.im| ≤ x/(chi.conductor : ℝ) :=
    ht.trans (div_le_div_of_nonneg_left (by linarith) hr0 hrd)
  have hg := primitive_high_gap hx (hrd.trans hq) hpr chi.primitiveCharacter_isPrimitive hrhalf
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz) hlo hheight
  linarith

end LiuWang.Proof.ZeroRegionFamily.Sharp
