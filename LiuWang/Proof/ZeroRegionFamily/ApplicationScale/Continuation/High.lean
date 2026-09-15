import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Quartic

/-! # 无绝对费用母式在全部x>=10的真实高/中阶付款 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform
open LiuWang.Proof.ZeroRegionFamily.LowOrderClosure (scaled_pole_paid cubic_powers_nonprincipal)

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation

theorem primitive_no_zero_of_poles {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    {A B : ℝ} (hA : 0 < A) (hA1 : A ≤ 17/50) (hB : 0 ≤ B)
    (hcost : (14379/A+46630*(691/2500)+B)*(A+3/40) < 24480)
    (hpoles : 14900*harmonicPole (chi^2) (1+A/Real.log x) (2*rho.im)+
      6000*harmonicPole (chi^3) (1+A/Real.log x) (3*rho.im)+
        1250*harmonicPole (chi^4) (1+A/Real.log x) (4*rho.im) ≤ B*Real.log x) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith
  have hw : 3/(40*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hu : 0 < A/Real.log x := div_pos hA hL
  have hu1 : A/Real.log x ≤ 3/20 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  have huL : Real.log x*(A/Real.log x)=A := by field_simp
  have hh := primitive_quartic_no_absolute_cost hc hp (by linarith) hz
    (sigma := 1+A/Real.log x) (by linarith) (by linarith)
  have hl := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hq ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hinv : 14379/(1+A/Real.log x-1)=(14379/A)*Real.log x := by
    rw [show 1+A/Real.log x-1=A/Real.log x by ring]
    field_simp
  rw [hinv] at hh
  have hupp : 24480/(1+A/Real.log x-rho.re) ≤
      (14379/A+46630*(691/2500)+B)*Real.log x := by linarith
  have hpaid := (div_le_iff₀ (show 0 < 1+A/Real.log x-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 3/40 := by
    have hh := (lt_div_iff₀ (show 0 < 40*Real.log x by positivity)).mp
      (show 1-rho.re < 3/(40*Real.log x) by linarith)
    nlinarith only [hh]
  have hcoef : 0 ≤ 14379/A+46630*(691/2500)+B := by positivity
  have hm := mul_le_mul_of_nonneg_left
    (show Real.log x*(1+A/Real.log x-rho.re) ≤ A+3/40 by nlinarith only [huL, hgap]) hcoef
  nlinarith only [hpaid, hm, hcost]

theorem primitive_scaled_high_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hv : 1/2 ≤ Real.log x*|rho.im|) : chi.LFunction rho ≠ 0 := by
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have h2 := scaled_pole_paid (chi^2) hL (by norm_num : (0 : ℝ) < 27/100)
    (by norm_num : (0 : ℝ) ≤ 1/2) hv (j := 2)
  have h3 := scaled_pole_paid (chi^3) hL (by norm_num : (0 : ℝ) < 27/100)
    (by norm_num : (0 : ℝ) ≤ 1/2) hv (j := 3)
  have h4 := scaled_pole_paid (chi^4) hL (by norm_num : (0 : ℝ) < 27/100)
    (by norm_num : (0 : ℝ) ≤ 1/2) hv (j := 4)
  apply primitive_no_zero_of_poles hx hq hc hp hr ht
    (A := 27/100) (B := 14900*(27/100)/((27/100)^2+1)+
      6000*(27/100)/((27/100)^2+9/4)+1250*(27/100)/((27/100)^2+4))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h2 h3 h4 ⊢
  linarith

theorem primitive_cubic_mid_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (h3 : chi^3=1) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hv : 1/5 ≤ Real.log x*|rho.im|) : chi.LFunction rho ≠ 0 := by
  obtain ⟨h2, h4⟩ := cubic_powers_nonprincipal chi hc h3
  have hmid := scaled_pole_paid (chi^3) (by linarith [log_scale_ge_34_15 hx] : 0 < Real.log x)
    (by norm_num : (0 : ℝ) < 27/100) (by norm_num : (0 : ℝ) ≤ 1/5) hv (j := 3)
  apply primitive_no_zero_of_poles hx hq hc hp hr ht
    (A := 27/100) (B := 6000*(27/100)/((27/100)^2+9/25))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [harmonicPole, if_neg h2, if_neg h4, mul_zero, zero_add, add_zero]
  unfold harmonicPole at hmid
  norm_num [h3] at hmid ⊢
  linarith

theorem primitive_other_orders_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (h2 : chi^2 ≠ 1) (h3 : chi^3 ≠ 1) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ)) :
    chi.LFunction rho ≠ 0 := by
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hp4 := harmonicPole_le_pole (chi^4) (sigma := 1+(3/10)/Real.log x)
    (by linarith [div_pos (by norm_num : (0 : ℝ) < 3/10) hL]) (4*rho.im)
  have hi : 1/(1+(3/10)/Real.log x-1)=(10/3)*Real.log x := by field_simp; ring
  rw [hi] at hp4
  apply primitive_no_zero_of_poles hx hq hc hp hr ht
    (A := 3/10) (B := 1250*(10/3)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [harmonicPole, if_neg h2, if_neg h3, mul_zero, zero_add]
  unfold harmonicPole at hp4
  linarith

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation
