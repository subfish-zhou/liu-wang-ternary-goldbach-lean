import LiuWang.Proof.ZeroRegionFamily.RealClosure.QuarticPositivity

/-! # 四次全部普通字符费用母式，以及前四幂本原非主分支的实际R10排除 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp
open scoped Classical

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

def harmonicBound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  if chi=1 then
    poleDifference sigma t+stechkinConductorCoeff*(Real.log (max 1 |t|)-Real.log Real.pi)+
      23/40-11*stechkinK/30+principalPrimeCost q sigma
  else
    stechkinConductorCoeff*(Real.log chi.conductor+Real.log (max 1 |t|)-Real.log Real.pi)+
      4/15+badPrimeCost chi sigma

theorem harmonicBound_paid {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤ harmonicBound chi sigma t := by
  unfold harmonicBound
  split_ifs with hc
  · subst chi
    exact principal_all_height hs hs1 t
  · exact imprimitive_damped_bound chi hc hs hs1 t

theorem ordinary_selected_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK rho.im+1/(sigma-rho.re) ≤
      stechkinConductorCoeff*(Real.log chi.conductor+Real.log (max 1 |rho.im|)-Real.log Real.pi)+
        4/15+badPrimeCost chi sigma := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hzp := primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz
  obtain ⟨p, hv⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hpr
    chi.primitiveCharacter_isPrimitive (by linarith) hzp
  have hsel := damped_selected_pair_le hpr chi.primitiveCharacter_isPrimitive hs rho.im p
    (by simpa only [hv] using hr)
  rw [hv] at hsel
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hpair := selected_pair_dominates hs (rho := rho) ⟨by linarith, hb⟩
  have hh := imprimitive_full_zero_sum_bound chi hc hs hs1 rho.im
  change _ ≤ primitiveZeroSum chi.primitiveCharacter sigma rho.im at hsel
  linarith

theorem quartic_actual_full_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-rho.re) ≤
      14379*(1/(sigma-1)-3/4-principalPrimeCost q sigma)+
      24480*(stechkinConductorCoeff*
        (Real.log chi.conductor+Real.log (max 1 |rho.im|)-Real.log Real.pi)+
          4/15+badPrimeCost chi sigma)+
      14900*harmonicBound (chi^2) sigma (2*rho.im)+
      6000*harmonicBound (chi^3) sigma (3*rho.im)+
      1250*harmonicBound (chi^4) sigma (4*rho.im) := by
  have hpos := quartic_stechkin_nonneg chi hs rho.im
  have hsel := ordinary_selected_bound chi hc hr hz hs hs1
  have h0 := principal_real_strong (q := q) hs hs1
  have h2 := harmonicBound_paid (chi^2) hs hs1 (2*rho.im)
  have h3 := harmonicBound_paid (chi^3) hs hs1 (3*rho.im)
  have h4 := harmonicBound_paid (chi^4) hs hs1 (4*rho.im)
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem log_max_harmonic_le (t : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Real.log (max 1 |(k : ℝ)*t|) ≤ Real.log (max 1 |t|)+(k : ℝ)-1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hm : 0 < max (1 : ℝ) |t| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hh : max 1 |(k : ℝ)*t| ≤ (k : ℝ)*max 1 |t| := by
    apply max_le
    · nlinarith [le_max_left (1 : ℝ) |t|]
    · rw [abs_mul, abs_of_pos hk0]
      exact mul_le_mul_of_nonneg_left (le_max_right 1 |t|) hk0.le
  have hl := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hh
  rw [Real.log_mul hk0.ne' hm.ne'] at hl
  linarith [Real.log_le_sub_one_of_pos hk0]

theorem quartic_primitive_powers_core {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (hc2 : chi^2 ≠ 1) (hp2 : (chi^2).IsPrimitive)
    (hc3 : chi^3 ≠ 1) (hp3 : (chi^3).IsPrimitive)
    (hc4 : chi^4 ≠ 1) (hp4 : (chi^4).IsPrimitive)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-rho.re) ≤ 14379/(sigma-1)+
      46630*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|)) := by
  have hpos := quartic_stechkin_nonneg chi hs rho.im
  have hsel := primitive_actual_selected_bound hc hp hr hz hs hs1
  have h0 := principal_real_strong (q := q) hs hs1
  have h2 := primitive_damped_bound hc2 hp2 hs hs1 (2*rho.im)
  have h3 := primitive_damped_bound hc3 hp3 hs hs1 (3*rho.im)
  have h4 := primitive_damped_bound hc4 hp4 hs hs1 (4*rho.im)
  have hh (k : ℕ) (hk : 1 ≤ k) := mul_le_mul_of_nonneg_left
    (log_max_harmonic_le rho.im hk) conductorCoeff_bounds.1
  have hl2 := hh 2 (by norm_num)
  have hl3 := hh 3 (by norm_num)
  have hl4 := hh 4 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hl2 hl3 hl4
  have hlogpi := mul_le_mul_of_nonneg_left log_pi_ge_one conductorCoeff_bounds.1
  have hk : 11/40 ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_le]
  have hcost := principalPrimeCost_nonneg q hs
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem quartic_primitive_powers_no_zero_ten {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (hc2 : chi^2 ≠ 1) (hp2 : (chi^2).IsPrimitive)
    (hc3 : chi^3 ≠ 1) (hp3 : (chi^3).IsPrimitive)
    (hc4 : chi^4 ≠ 1) (hp4 : (chi^4).IsPrimitive)
    {rho : ℂ} (hr : 1-1/(10*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ)) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hL := log_scale_ge hx
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
  have hh := quartic_primitive_powers_core hc hp hc2 hp2 hc3 hp3 hc4 hp4
    (by linarith) hz (sigma := 1+u) (by linarith) (by linarith)
  rw [hinv] at hh
  have hl := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  have hupp : 24480/(1+u-rho.re) ≤ 280967*Real.log x/5 := by nlinarith
  have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/10 := by
    have hh := (lt_div_iff₀ (show 0 < 10*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(10*Real.log x) by linarith)
    nlinarith
  nlinarith

end LiuWang.Proof.ZeroRegionFamily.RealClosure
