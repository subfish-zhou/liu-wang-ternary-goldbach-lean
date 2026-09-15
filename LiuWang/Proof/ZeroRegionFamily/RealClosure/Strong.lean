import LiuWang.Proof.ZeroRegionFamily.RealClosure.QuarticBudget

/-! # 同域保更强9.65本原幂分支，完整字符族仍为R24 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

theorem conductorCoeff_le_691_2500 : stechkinConductorCoeff ≤ 691/2500 := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hk : 559/1250 ≤ stechkinK := by
    dsimp [stechkinK]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  dsimp [stechkinConductorCoeff]
  linarith

theorem log_scale_ge_34_15 {x : ℝ} (hx : 10 ≤ x) : 34/15 ≤ Real.log x := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5/4)
  have htwo := Real.log_two_gt_d9
  have he : Real.log (10 : ℝ)=3*Real.log 2+Real.log (5/4) := by
    rw [show (10 : ℝ)=2^3*(5/4) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 10) hx
  rw [he] at hl
  norm_num at hh
  linarith

theorem quartic_primitive_powers_no_zero_193_20 {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (hc2 : chi^2 ≠ 1) (hp2 : (chi^2).IsPrimitive)
    (hc3 : chi^3 ≠ 1) (hp3 : (chi^3).IsPrimitive)
    (hc4 : chi^4 ≠ 1) (hp4 : (chi^4).IsPrimitive)
    {rho : ℂ} (hr : 1-1/((193/20)*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ)) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hL := log_scale_ge_34_15 hx
  have hL0 : 0 < Real.log x := by linarith
  have hw : 1/((193/20)*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  let u := 17/(50*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have huL : Real.log x*u=17/50 := by dsimp [u]; field_simp
  have hinv : 14379/(1+u-1)=(718950/17)*Real.log x := by dsimp [u]; field_simp; ring
  have hh := quartic_primitive_powers_core hc hp hc2 hp2 hc3 hp3 hc4 hp4
    (by linarith) hz (sigma := 1+u) (by linarith) (by linarith)
  rw [hinv] at hh
  have hl := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  have hupp : 24480/(1+u-rho.re) ≤ (718950/17+46630*(691/2500))*Real.log x := by nlinarith
  have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 20/193 := by
    have hh := (lt_div_iff₀ (show 0 < (193/20)*Real.log x by positivity)).mp
      (show 1-rho.re < 1/((193/20)*Real.log x) by linarith)
    nlinarith
  nlinarith

end LiuWang.Proof.ZeroRegionFamily.RealClosure
