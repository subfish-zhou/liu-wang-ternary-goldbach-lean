import LiuWang.Proof.ZeroRegionFamily.Uniform.Quartic

/-! # 低高度二次非实分支补足完整R20；不偏移使用中心反射核 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

theorem quadratic_low_core {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2=1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0) (ht : |rho.im| ≤ 1/2)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    4/(sigma-rho.re) ≤ 3/(sigma-1)+
      (sigma-1)/((sigma-1)^2+4*rho.im^2)+4*stechkinConductorCoeff*Real.log q := by
  have hpos := stechkin_combination_nonneg chi hs rho.im
  rw [hsq] at hpos
  have hzero := primitive_actual_selected_bound hc hp hr hz hs hs1
  have hreal := principal_real_strong (q := q) hs hs1
  have hall := principal_all_height (q := q) hs hs1 (2*rho.im)
  rw [max_eq_left (by linarith), Real.log_one] at hzero
  rw [max_eq_left (by rw [abs_mul]; norm_num; linarith), Real.log_one] at hall
  have hpole : poleDifference sigma (2*rho.im) ≤
      (sigma-1)/((sigma-1)^2+4*rho.im^2) := by
    have hn : 0 ≤ (1/((stechkinSigma sigma : ℂ)-1+I*((2*rho.im : ℝ) : ℂ))).re := by
      rw [one_div, Complex.inv_re]
      apply div_nonneg _ (Complex.normSq_nonneg _)
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
      linarith [stechkinSigma_ge hs]
    have he : (1/((sigma : ℂ)-1+I*((2*rho.im : ℝ) : ℂ))).re =
        (sigma-1)/((sigma-1)^2+4*rho.im^2) := by
      simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      congr 1
      ring
    dsimp [poleDifference]
    rw [he]
    exact sub_le_self _ (mul_nonneg stechkinK_mem.1 hn)
  have hpi := mul_nonneg conductorCoeff_bounds.1
    (show 0 ≤ Real.log Real.pi by linarith [ChebyshevBound.HighHeight.log_pi_ge_one])
  have hcost := principalPrimeCost_nonneg q hs
  have hk := stechkinK_mem.1
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem primitive_quadratic_low_no_zero_twenty {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2=1)
    {rho : ℂ} (hr : 1-1/(20*Real.log x) < rho.re) (hi : rho.im ≠ 0)
    (ht : |rho.im| ≤ 1/2) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL := log_scale_ge_34_15 hx
  have hL0 : 0 < Real.log x := by linarith
  have hlogq : Real.log q ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast NeZero.pos q) hq
  have hw : 1/(20*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hgap : (1-rho.re)*Real.log x < 1/20 := by
    have hh := (lt_div_iff₀ (show 0 < 20*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(20*Real.log x) by linarith)
    nlinarith
  by_cases hlo : |rho.im| ≤ 1/(2*Real.log x)
  · let u := 1/Real.log x
    have hu : 0 < u := by dsimp [u]; positivity
    have hu1 : u ≤ 1 := by dsimp [u]; exact (div_le_one hL0).mpr (by linarith)
    have huL : Real.log x*u=1 := by dsimp [u]; field_simp
    have hh := quadratic_real_axis_pair hc hp hsq (by linarith) hz hi
      (sigma := 1+u) (by linarith) (by linarith)
    have hinv : 1/(1+u-1)=Real.log x := by dsimp [u]; field_simp; ring
    rw [hinv] at hh
    have hd : 0 < (1+u-rho.re)^2+rho.im^2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith)) (sq_nonneg _)
    have hpaid := (div_le_iff₀ hd).mp
      (show 2*(1+u-rho.re)/((1+u-rho.re)^2+rho.im^2) ≤ 3*Real.log x/2 by linarith)
    have habs : Real.log x*|rho.im| ≤ 1/2 := by
      have hh := (le_div_iff₀ (show 0 < 2*Real.log x by positivity)).mp hlo
      nlinarith
    have htsq : (Real.log x)^2*rho.im^2 ≤ 1/4 := by
      have hh := mul_nonneg (show 0 ≤ Real.log x*|rho.im| by positivity)
        (show 0 ≤ 1/2-Real.log x*|rho.im| by linarith)
      nlinarith [sq_abs rho.im]
    have ha : 1 ≤ Real.log x*(1+u-rho.re) := by nlinarith
    have ha1 : Real.log x*(1+u-rho.re) ≤ 21/20 := by nlinarith
    have hasq := mul_nonneg (show 0 ≤ Real.log x*(1+u-rho.re)-1 by linarith)
      (show 0 ≤ 21/20-Real.log x*(1+u-rho.re) by linarith)
    have hm := mul_le_mul_of_nonneg_left hpaid hL0.le
    nlinarith
  · let u := 17/(50*Real.log x)
    have hu : 0 < u := by dsimp [u]; positivity
    have hu1 : u ≤ 3/20 := by
      dsimp [u]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    have huL : Real.log x*u=17/50 := by dsimp [u]; field_simp
    have htL : 1/2 ≤ Real.log x*|rho.im| := by
      have hh := (div_le_iff₀ (show 0 < 2*Real.log x by positivity)).mp (le_of_not_ge hlo)
      nlinarith
    have htsq : 1/4 ≤ (Real.log x)^2*rho.im^2 := by
      have hh := mul_nonneg (show 0 ≤ Real.log x*|rho.im|-1/2 by linarith)
        (show 0 ≤ Real.log x*|rho.im|+1/2 by positivity)
      nlinarith [sq_abs rho.im]
    have husq : (Real.log x)^2*u^2=(17/50 : ℝ)^2 := by nlinarith [sq_nonneg (Real.log x*u-17/50)]
    have hd : 0 < u^2+4*rho.im^2 := by positivity
    have hpole : u/(u^2+4*rho.im^2) ≤ 31*Real.log x/100 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    have hh := quadratic_low_core hc hp hsq (by linarith) hz ht
      (sigma := 1+u) (by linarith) (by linarith)
    rw [show 1+u-1=u by ring] at hh
    have hinv : 3/u=(150/17)*Real.log x := by dsimp [u]; field_simp; norm_num
    rw [hinv] at hh
    have hl := mul_le_mul_of_nonneg_left hlogq
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) conductorCoeff_bounds.1)
    have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
    have hupp : 4/(1+u-rho.re) ≤ (150/17+31/100+4*(691/2500))*Real.log x := by
      nlinarith only [hh, hpole, hl, hk]
    have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
    nlinarith only [hpaid, huL, hgap]

theorem ordinary_zero_real_twenty {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hz : chi.LFunction rho=0) : chi^2=1 ∧ rho.im=0 := by
  obtain ⟨hsq, hlo⟩ := ordinary_zero_localized_twenty hx hq chi hc hr ht hz
  refine ⟨hsq, ?_⟩
  by_contra hi
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hL := log_scale_ge hx
  have hw : 1/(20*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  exact primitive_quadratic_low_no_zero_twenty hx (hcq.trans hq)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi hsq)
    hr hi hlo.le (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz)

end LiuWang.Proof.ZeroRegionFamily.Uniform
