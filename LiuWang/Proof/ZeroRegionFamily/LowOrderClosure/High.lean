import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Pole

/-! # 四次全部主谐波付款，将R14高支降至1/(2log x) -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem scaled_high_no_zero_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hv : 1/2 ≤ Real.log x*|rho.im|) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  let u := (27/100)/Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ hL).mpr
    linarith
  have huL : Real.log x*u=27/100 := by dsimp [u]; field_simp
  have h2 := scaled_pole_paid (chi^2) hL (by norm_num : (0 : ℝ) < 27/100)
    (by norm_num : (0 : ℝ) ≤ 1/2) hv (j := 2)
  have h3 := scaled_pole_paid (chi^3) hL (by norm_num : (0 : ℝ) < 27/100)
    (by norm_num : (0 : ℝ) ≤ 1/2) hv (j := 3)
  have h4 := scaled_pole_paid (chi^4) hL (by norm_num : (0 : ℝ) < 27/100)
    (by norm_num : (0 : ℝ) ≤ 1/2) hv (j := 4)
  have hh := quartic_joint_all_height chi hc (by linarith) hz
    (sigma := 1+u) (by linarith) (by linarith)
  have hl := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hs := principalPrimeCost_nonneg q (sigma := 1+u) (by linarith)
  have hinv : 14379/(1+u-1)=(14379/(27/100))*Real.log x := by dsimp [u]; field_simp; ring
  rw [hinv] at hh
  change harmonicPole (chi^2) (1+u) (2*rho.im) ≤ _ at h2
  change harmonicPole (chi^3) (1+u) (3*rho.im) ≤ _ at h3
  change harmonicPole (chi^4) (1+u) (4*rho.im) ≤ _ at h4
  have hupp : 24480/(1+u-rho.re) ≤
      (14379/(27/100)+46630*(691/2500)+139890/160+
        14900*(27/100)/((27/100)^2+4/4)+6000*(27/100)/((27/100)^2+9/4)+
          1250*(27/100)/((27/100)^2+16/4))*Real.log x := by
    norm_num at h2 h3 h4 ⊢
    nlinarith only [hh, hl, hk, hs, hx, h2, h3, h4]
  have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
    nlinarith only [hh]
  nlinarith only [hpaid, huL, hgap]

theorem cubic_powers_nonprincipal {q : ℕ} (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (h3 : chi^3=1) : chi^2 ≠ 1 ∧ chi^4 ≠ 1 := by
  constructor
  · intro h2
    have he : chi^3=chi := by rw [show (3 : ℕ)=2+1 by rfl, pow_succ, h2, one_mul]
    exact hc (he.symm.trans h3)
  · intro h4
    have he : chi^4=chi := by rw [show (4 : ℕ)=3+1 by rfl, pow_succ, h3, one_mul]
    exact hc (he.symm.trans h4)

theorem cubic_scaled_high_no_zero_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hc3 : chi^3=1) {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hv : 1/5 ≤ Real.log x*|rho.im|) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  let u := (27/100)/Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ hL).mpr
    linarith
  have huL : Real.log x*u=27/100 := by dsimp [u]; field_simp
  have h3 := scaled_pole_paid (chi^3) hL (by norm_num : (0 : ℝ) < 27/100)
    (by norm_num : (0 : ℝ) ≤ 1/5) hv (j := 3)
  have hh := quartic_joint_all_height chi hc (by linarith) hz
    (sigma := 1+u) (by linarith) (by linarith)
  obtain ⟨hc2, hc4⟩ := cubic_powers_nonprincipal chi hc hc3
  have hp2 : harmonicPole (chi^2) (1+u) (2*rho.im)=0 := if_neg hc2
  have hp4 : harmonicPole (chi^4) (1+u) (4*rho.im)=0 := if_neg hc4
  rw [hp2, hp4] at hh
  have hl := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hs := principalPrimeCost_nonneg q (sigma := 1+u) (by linarith)
  have hinv : 14379/(1+u-1)=(14379/(27/100))*Real.log x := by dsimp [u]; field_simp; ring
  rw [hinv] at hh
  change harmonicPole (chi^3) (1+u) (3*rho.im) ≤ _ at h3
  have hupp : 24480/(1+u-rho.re) ≤
      (14379/(27/100)+46630*(691/2500)+139890/160+
        6000*(27/100)/((27/100)^2+9/25))*Real.log x := by
    norm_num at h3 ⊢
    nlinarith only [hh, hl, hk, hs, hx, h3]
  have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
    nlinarith only [hh]
  nlinarith only [hpaid, huL, hgap]

theorem powers_two_three_no_zero_fourteen_refined {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (h2 : chi^2 ≠ 1) (h3 : chi^3 ≠ 1)
    {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL : 0 < Real.log x := by linarith
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
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hs := principalPrimeCost_nonneg q (sigma := 1+u) (by linarith)
  have hupp : 24480/(1+u-rho.re) ≤
      (15629*(10/3)+46630*(691/2500)+139890/160)*Real.log x := by
    simp only [harmonicPole] at hp4
    nlinarith only [hh, hp4, hl, hk, hs, hx]
  have hpaid := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
    nlinarith only [hh]
  nlinarith only [hpaid, hgap, huL]

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
