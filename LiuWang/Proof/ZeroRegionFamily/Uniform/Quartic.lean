import LiuWang.Proof.ZeroRegionFamily.Uniform.Conductor

/-! # 任意普通字符的四次联合付款；不要求任何字符幂本原 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

theorem nonprincipal_budget_joint {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    stechkinConductorCoeff*(Real.log chi.conductor+Real.log (max 1 |t|)-Real.log Real.pi)+
      4/15+badPrimeCost chi sigma ≤
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+3 := by
  linarith [conductor_euler_joint chi hs, small_prime_log_cost_le_two]

theorem harmonic_joint_paid {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ)
    (hbranch : chi ≠ 1 ∨ 1 ≤ |t|) :
    harmonicBound chi sigma t ≤
      stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+3 := by
  unfold harmonicBound
  split_ifs with hc
  · have ht := hbranch.resolve_left (not_not.mpr hc)
    have hp := poleDifference_high_nonpos hs hs1 ht
    have he := principal_euler_joint q hs
    have hk := stechkinK_mem.1
    nlinarith [small_prime_log_cost_le_two]
  · exact nonprincipal_budget_joint chi hs t

theorem quartic_joint_core {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    (h2 : chi^2 ≠ 1 ∨ 1 ≤ |2*rho.im|)
    (h3 : chi^3 ≠ 1 ∨ 1 ≤ |3*rho.im|)
    (h4 : chi^4 ≠ 1 ∨ 1 ≤ |4*rho.im|)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-rho.re) ≤ 14379/(sigma-1)+
      46630*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|))+
        139890-14379*principalPrimeCost q sigma := by
  have hh := quartic_actual_full_bound chi hc hr hz hs hs1
  have hmain := nonprincipal_budget_joint chi hs rho.im
  have hb2 := harmonic_joint_paid (chi^2) hs hs1 (2*rho.im) h2
  have hb3 := harmonic_joint_paid (chi^3) hs hs1 (3*rho.im) h3
  have hb4 := harmonic_joint_paid (chi^4) hs hs1 (4*rho.im) h4
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

theorem quartic_joint_no_zero_ten {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-1/(10*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ))
    (h2 : chi^2 ≠ 1 ∨ 1 ≤ |2*rho.im|)
    (h3 : chi^3 ≠ 1 ∨ 1 ≤ |3*rho.im|)
    (h4 : chi^4 ≠ 1 ∨ 1 ≤ |4*rho.im|) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL0 : 0 < Real.log x := by linarith
  have hw : 1/(10*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  let u := 1/(3*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have huL : Real.log x*u=1/3 := by dsimp [u]; field_simp
  have hinv : 14379/(1+u-1)=43137*Real.log x := by dsimp [u]; field_simp; ring
  have hh := quartic_joint_core chi hc (by linarith) hz h2 h3 h4
    (sigma := 1+u) (by linarith) (by linarith)
  rw [hinv] at hh
  have hl := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  have hs := principalPrimeCost_nonneg q (sigma := 1+u) (by linarith)
  have hupp : 24480/(1+u-rho.re) ≤
      (43137+46630*(691/2500)+139890/400)*Real.log x := by nlinarith
  have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/10 := by
    have hh := (lt_div_iff₀ (show 0 < 10*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(10*Real.log x) by linarith)
    nlinarith
  nlinarith

theorem all_nonprincipal_high_no_zero_ten {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-1/(10*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hlo : 1/2 ≤ |rho.im|) : chi.LFunction rho ≠ 0 := by
  have hmul (k : ℝ) (hk : 2 ≤ k) : 1 ≤ |k*rho.im| := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    nlinarith
  exact quartic_joint_no_zero_ten hx hq chi hc hr ht
    (Or.inr (hmul 2 (by norm_num))) (Or.inr (hmul 3 (by norm_num)))
    (Or.inr (hmul 4 (by norm_num)))

theorem all_nonprincipal_powers_no_zero_ten {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (h2 : chi^2 ≠ 1) (h3 : chi^3 ≠ 1) (h4 : chi^4 ≠ 1)
    {rho : ℂ} (hr : 1-1/(10*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) : chi.LFunction rho ≠ 0 :=
  quartic_joint_no_zero_ten hx hq chi hc hr ht (Or.inl h2) (Or.inl h3) (Or.inl h4)

end LiuWang.Proof.ZeroRegionFamily.Uniform
