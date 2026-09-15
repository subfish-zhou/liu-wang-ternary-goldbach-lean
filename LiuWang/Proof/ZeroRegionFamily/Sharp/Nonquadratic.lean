import LiuWang.Proof.ZeroRegionFamily.Sharp.Selected

/-! # 实际Stechkin费用接回连续有限区域：非二次分支R=20 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem conductorCoeff_bounds : 0 ≤ stechkinConductorCoeff ∧ stechkinConductorCoeff ≤ 7/25 := by
  dsimp [stechkinConductorCoeff]
  constructor <;> linarith [stechkinK_mem.2, stechkinK_ge]

theorem badPrimeCost_le_principal {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) : badPrimeCost chi sigma ≤ principalPrimeCost q sigma := by
  apply sum_le_sum
  intro p hp
  split_ifs
  · exact primeCost_nonneg (Nat.prime_of_mem_primeFactors hp) hs
  · exact le_rfl

theorem principalPrimeCost_nonneg (q : ℕ) {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ principalPrimeCost q sigma :=
  sum_nonneg (fun _ hp => primeCost_nonneg (Nat.prime_of_mem_primeFactors hp) hs)

theorem imprimitive_level_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+
        4/15+principalPrimeCost q sigma := by
  have hh := imprimitive_damped_bound chi hc hs hs1 t
  have he := badPrimeCost_le_principal chi hs
  have hl : Real.log chi.conductor ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
    (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
  have hp := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  nlinarith

theorem nonquadratic_core_function {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2 ≠ 1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    4/(sigma-rho.re) ≤ 3/(sigma-1)+
      stechkinConductorCoeff*(5*Real.log q+4*Real.log (max 1 |rho.im|)+
        Real.log (max 1 |2*rho.im|)-5*Real.log Real.pi)-11/12-
      2*principalPrimeCost q sigma := by
  have hpos := stechkin_combination_nonneg chi hs rho.im
  have hzero := primitive_actual_selected_bound hc hp hr hz hs hs1
  have hprincipal := principal_real_strong (q := q) hs hs1
  have hsquare := imprimitive_level_bound (chi^2) hsq hs hs1 (2*rho.im)
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem log_max_double_le (t : ℝ) :
    Real.log (max 1 |2*t|) ≤ Real.log 2+Real.log (max 1 |t|) := by
  rw [← Real.log_mul (by norm_num) (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))]
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply max_le
  · linarith [le_max_left (1 : ℝ) |t|]
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (le_max_right 1 |t|) (by norm_num)

theorem nonquadratic_core {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2 ≠ 1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    4/(sigma-rho.re) ≤ 3/(sigma-1)+
      5*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|)) := by
  have hh := nonquadratic_core_function hc hp hsq hr hz hs hs1
  have hlog := mul_le_mul_of_nonneg_left (log_max_double_le rho.im) conductorCoeff_bounds.1
  have hconst : stechkinConductorCoeff*(Real.log 2-5*Real.log Real.pi) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos conductorCoeff_bounds.1
      (by linarith [Real.log_two_lt_d9, log_pi_ge_one])
  have hcost := principalPrimeCost_nonneg q hs
  nlinarith

theorem log_scale_ge {x : ℝ} (hx : 10 ≤ x) : 9/4 ≤ Real.log x := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5/4)
  have htwo := Real.log_two_gt_d9
  have he : Real.log (10 : ℝ)=3*Real.log 2+Real.log (5/4) := by
    rw [show (10 : ℝ)=2^3*(5/4) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 10) hx
  rw [he] at hl
  norm_num at hh
  linarith

theorem conductor_height_log_max_le {x : ℝ} {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ x) {t : ℝ} (ht : |t| ≤ x/(q : ℝ)) :
    Real.log q+Real.log (max 1 |t|) ≤ Real.log x := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  rw [← Real.log_mul hq0.ne' (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))]
  apply Real.log_le_log (by positivity)
  rw [mul_max_of_nonneg _ _ hq0.le]
  apply max_le (by simpa using hq)
  have hh := (le_div_iff₀ hq0).mp ht
  nlinarith

theorem primitive_nonquadratic_finite_gap {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hsq : chi^2 ≠ 1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    (ht : |rho.im| ≤ x/(q : ℝ)) : 1/(20*Real.log x) ≤ 1-rho.re := by
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  have hlog := conductor_height_log_max_le hq ht
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
  have hinv : 3/(1+u-1)=9*Real.log x := by dsimp [u]; field_simp; ring
  have hcore := nonquadratic_core hc hp hsq hr hz (sigma := 1+u) (by linarith) (by linarith)
  rw [hinv] at hcore
  have h1 := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) conductorCoeff_bounds.1)
  have h2 := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  have hupper : 4/(1+u-rho.re) ≤ (52/5)*Real.log x := by nlinarith
  have hden : 0 < 1+u-rho.re := by linarith
  have hpaid := (div_le_iff₀ hden).mp hupper
  by_contra h
  have hgap : (1-rho.re)*Real.log x < 1/20 := by
    have hh := (lt_div_iff₀ (show 0 < 20*Real.log x by positivity)).mp (lt_of_not_ge h)
    nlinarith
  nlinarith

theorem nonquadratic_no_zero_twenty {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hsq : chi^2 ≠ 1)
    {rho : ℂ} (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ)) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hc : chi ≠ 1 := by intro h; simp [h] at hsq
  have hL := log_scale_ge hx
  have hw : 1/(20*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hrhalf : 1/2 < rho.re := by linarith
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hps := BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one chi hsq
  have hrd : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hr0 : (0 : ℝ) < chi.conductor := by exact_mod_cast NeZero.pos chi.conductor
  have hheight : |rho.im| ≤ x/(chi.conductor : ℝ) :=
    ht.trans (div_le_div_of_nonneg_left (by linarith) hr0 hrd)
  have hg := primitive_nonquadratic_finite_gap hx (hrd.trans hq) hpr
    chi.primitiveCharacter_isPrimitive hps hrhalf
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz) hheight
  linarith

end LiuWang.Proof.ZeroRegionFamily.Sharp
