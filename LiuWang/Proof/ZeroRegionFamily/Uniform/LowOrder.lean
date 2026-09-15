import LiuWang.Proof.ZeroRegionFamily.Uniform.Family

/-! # 任意高度的实际变主极点母式与四阶字符全部高度R14 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open scoped Classical

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

def harmonicPole {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  if chi=1 then poleDifference sigma t else 0

theorem harmonic_joint_all_height {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    harmonicBound chi sigma t ≤ harmonicPole chi sigma t+
      stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+3 := by
  unfold harmonicBound harmonicPole
  split_ifs with hc
  · have he := principal_euler_joint q hs
    have hk := stechkinK_mem.1
    nlinarith [small_prime_log_cost_le_two]
  · simpa using nonprincipal_budget_joint chi hs t

theorem quartic_joint_all_height {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-rho.re) ≤ 14379/(sigma-1)+
      46630*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|))+
        139890+14900*harmonicPole (chi^2) sigma (2*rho.im)+
          6000*harmonicPole (chi^3) sigma (3*rho.im)+
            1250*harmonicPole (chi^4) sigma (4*rho.im)-14379*principalPrimeCost q sigma := by
  have hh := quartic_actual_full_bound chi hc hr hz hs hs1
  have hmain := nonprincipal_budget_joint chi hs rho.im
  have hb2 := harmonic_joint_all_height (chi^2) hs (2*rho.im)
  have hb3 := harmonic_joint_all_height (chi^3) hs (3*rho.im)
  have hb4 := harmonic_joint_all_height (chi^4) hs (4*rho.im)
  have hl (k : ℕ) (hk : 1 ≤ k) := mul_le_mul_of_nonneg_left
    (log_max_harmonic_le rho.im hk) conductorCoeff_bounds.1
  have hl2 := hl 2 (by norm_num)
  have hl3 := hl 3 (by norm_num)
  have hl4 := hl 4 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hl2 hl3 hl4
  have hp := mul_le_mul_of_nonneg_left ChebyshevBound.HighHeight.log_pi_ge_one
    conductorCoeff_bounds.1
  have hk := conductorCoeff_bounds.1
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem poleDifference_le_pole {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    poleDifference sigma t ≤ 1/(sigma-1) := by
  have hu : 0 < sigma-1 := by linarith
  have hv : 0 < stechkinSigma sigma-1 := by linarith [stechkinSigma_ge hs]
  have hh : (sigma-1)/((sigma-1)^2+t^2) ≤ 1/(sigma-1) := by
    apply (div_le_div_iff₀ (by positivity) hu).mpr
    nlinarith [sq_nonneg t]
  have hn : 0 ≤ stechkinK*((stechkinSigma sigma-1)/((stechkinSigma sigma-1)^2+t^2)) :=
    mul_nonneg stechkinK_mem.1 (by positivity)
  simp only [poleDifference, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.add_im,
    Complex.mul_im, Complex.one_im, zero_mul, one_mul, sub_zero, add_zero, zero_add] at *
  simp only [pow_two] at hh hn
  linarith

theorem harmonicPole_le_pole {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) : harmonicPole chi sigma t ≤ 1/(sigma-1) := by
  unfold harmonicPole
  split_ifs
  · exact poleDifference_le_pole hs t
  · positivity

theorem powers_two_three_no_zero_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (h2 : chi^2 ≠ 1) (h3 : chi^3 ≠ 1)
    {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL0 : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  let u := 3/(10*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have huL : Real.log x*u=3/10 := by dsimp [u]; field_simp
  have hinv : 1/u=(10/3)*Real.log x := by dsimp [u]; field_simp
  have hh := quartic_joint_all_height chi hc (by linarith) hz
    (sigma := 1+u) (by linarith) (by linarith)
  have hp4 := harmonicPole_le_pole (chi^4) (sigma := 1+u) (by linarith) (4*rho.im)
  simp only [harmonicPole, if_neg h2, if_neg h3, mul_zero, add_zero,
    show 1+u-1=u by ring] at hh
  rw [show 1+u-1=u by ring, hinv] at hp4
  have hinv' : 14379/u=14379*(10/3)*Real.log x := by rw [div_eq_mul_one_div, hinv]; ring
  rw [hinv'] at hh
  have hl := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  have hs := principalPrimeCost_nonneg q (sigma := 1+u) (by linarith)
  have hupp : 24480/(1+u-rho.re) ≤
      (15629*(10/3)+46630*(691/2500)+139890/400)*Real.log x := by
    simp only [harmonicPole] at hp4
    nlinarith only [hh, hp4, hl, hk, hs, hx]
  have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
    nlinarith only [hh]
  nlinarith only [hpaid, hgap, huL]

theorem order_four_no_zero_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (h2 : chi^2 ≠ 1) (h4 : chi^4=1)
    {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) : chi.LFunction rho ≠ 0 := by
  have hc : chi ≠ 1 := by intro h; apply h2; simp [h]
  have h3 : chi^3 ≠ 1 := by
    intro h
    have hh : chi^4=chi := by rw [show (4 : ℕ)=3+1 by rfl, pow_succ, h, one_mul]
    exact hc (hh.symm.trans h4)
  exact powers_two_three_no_zero_fourteen hx hq chi hc h2 h3 hr ht

end LiuWang.Proof.ZeroRegionFamily.Uniform
