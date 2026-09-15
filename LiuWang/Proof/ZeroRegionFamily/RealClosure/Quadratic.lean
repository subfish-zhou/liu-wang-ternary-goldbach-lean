import LiuWang.Proof.ZeroRegionFamily.Sharp.Consumer

/-! # 二次非实零点：实轴共轭双核与低高度实际主极点共同给R24 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

theorem quadratic_pole_core {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2=1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    4/(sigma-rho.re) ≤ 3/(sigma-1)+
      (sigma-1)/((sigma-1)^2+4*rho.im^2)+
      5*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|)) := by
  have hpos := stechkin_combination_nonneg chi hs rho.im
  have hzero := primitive_actual_selected_bound hc hp hr hz hs hs1
  have hreal := principal_real_strong (q := q) hs hs1
  have hall := principal_all_height (q := q) hs hs1 (2*rho.im)
  have hlog := mul_le_mul_of_nonneg_left (log_max_double_le rho.im) conductorCoeff_bounds.1
  have hqlog := mul_nonneg conductorCoeff_bounds.1 (Real.log_natCast_nonneg q)
  have hconst : stechkinConductorCoeff*(Real.log 2-5*Real.log Real.pi) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos conductorCoeff_bounds.1
      (by linarith [Real.log_two_lt_d9, log_pi_ge_one])
  have hcost := principalPrimeCost_nonneg q hs
  have hk := stechkinK_mem.1
  have hge := stechkinSigma_ge hs
  have hpole : poleDifference sigma (2*rho.im) ≤
      (sigma-1)/((sigma-1)^2+4*rho.im^2) := by
    have hn : 0 ≤ (1/((stechkinSigma sigma : ℂ)-1+I*((2*rho.im : ℝ) : ℂ))).re := by
      rw [one_div, Complex.inv_re]
      apply div_nonneg _ (Complex.normSq_nonneg _)
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
      linarith
    have he : (1/((sigma : ℂ)-1+I*((2*rho.im : ℝ) : ℂ))).re =
        (sigma-1)/((sigma-1)^2+4*rho.im^2) := by
      simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      congr 1
      ring
    dsimp [poleDifference]
    rw [he]
    exact sub_le_self _ (mul_nonneg hk hn)
  rw [hsq] at hpos
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem quadratic_real_axis_pair {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2=1)
    {rho : ℂ} (hr : 0 < rho.re) (hz : chi.LFunction rho=0) (hi : rho.im ≠ 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    2*(sigma-rho.re)/((sigma-rho.re)^2+rho.im^2) ≤ 1/(sigma-1)+Real.log q/2 := by
  obtain ⟨p, hv⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hc hp hr hz
  obtain ⟨r, hrv⟩ := exists_quadratic_conjugateZeroIndex hc hp hsq p
  have hne : p ≠ r := by
    intro he
    have hh := congrArg Complex.im hrv
    rw [← he, hv, Complex.conj_im] at hh
    exact hi (by linarith)
  have hh := two_real_kernel_le hc hp p r hne hs hs2
  rw [hrv, hv, conjugatePairKernel_re] at hh
  exact hh

theorem primitive_quadratic_nonreal_gap_twentyfour {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2=1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    (hi : rho.im ≠ 0) (ht : |rho.im| ≤ x/(q : ℝ)) :
    1/(24*Real.log x) ≤ 1-rho.re := by
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  have hlogq : Real.log q ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast NeZero.pos q) hq
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  by_contra hg
  have hgap : (1-rho.re)*Real.log x < 1/24 := by
    have hh := (lt_div_iff₀ (show 0 < 24*Real.log x by positivity)).mp (lt_of_not_ge hg)
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
    have hd : 0 < (1+u-rho.re)^2+rho.im^2 := by
      exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith)) (sq_nonneg _)
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
    have ha1 : Real.log x*(1+u-rho.re) < 25/24 := by nlinarith
    have hasq := mul_nonneg (show 0 ≤ Real.log x*(1+u-rho.re) by linarith)
      (show 0 ≤ 25/24-Real.log x*(1+u-rho.re) by linarith)
    have hm := mul_le_mul_of_nonneg_left hpaid hL0.le
    nlinarith
  · let u := 3/(10*Real.log x)
    have hu : 0 < u := by dsimp [u]; positivity
    have hu1 : u ≤ 3/20 := by
      dsimp [u]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    have huL : Real.log x*u=3/10 := by dsimp [u]; field_simp
    have htL : 1/2 ≤ Real.log x*|rho.im| := by
      have hh := (div_le_iff₀ (show 0 < 2*Real.log x by positivity)).mp (le_of_not_ge hlo)
      nlinarith
    have htsq : 1/4 ≤ (Real.log x)^2*rho.im^2 := by
      have hh := mul_nonneg (show 0 ≤ Real.log x*|rho.im|-1/2 by linarith)
        (show 0 ≤ Real.log x*|rho.im|+1/2 by positivity)
      nlinarith [sq_abs rho.im]
    have hd : 0 < u^2+4*rho.im^2 := by positivity
    have hpole : u/(u^2+4*rho.im^2) ≤ 3*Real.log x/10 := by
      apply (div_le_iff₀ hd).mpr
      have hh : 0 ≤ (Real.log x)^2*u^2 := by positivity
      nlinarith
    have hh := quadratic_pole_core hc hp hsq hr hz
      (sigma := 1+u) (by linarith) (by linarith)
    rw [show 1+u-1=u by ring] at hh
    have hinv : 3/u=10*Real.log x := by dsimp [u]; field_simp
    rw [hinv] at hh
    have hlog := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) conductorCoeff_bounds.1)
    have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
    have hupper : 4/(1+u-rho.re) ≤ 117*Real.log x/10 := by nlinarith
    have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupper
    nlinarith

end LiuWang.Proof.ZeroRegionFamily.RealClosure
