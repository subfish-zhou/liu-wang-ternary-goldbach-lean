import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.High

/-! # 全部x>=10：低阶、普通非主、独立主字符及真实实单性 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.LowOrderClosure (cubic_real_axis_single coupled_kernel_contradiction)

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation

theorem region_re_half {x : ℝ} {rho : ℂ} (hx : 10 ≤ x)
    (hr : 1-3/(40*Real.log x) < rho.re) : 1/2 < rho.re := by
  have hl := log_scale_ge_34_15 hx
  have hw : 3/(40*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  linarith

theorem primitive_low_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re)
    (hbranch : (chi^3=1 ∧ Real.log x*|rho.im| ≤ 1/5) ∨
      (chi^2=1 ∧ rho.im ≠ 0 ∧ Real.log x*|rho.im| ≤ 1/2)) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hhalf := region_re_half hx hr
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hgap : (1-rho.re)*Real.log x < 3/40 := by
    have hh := (lt_div_iff₀ (show 0 < 40*Real.log x by positivity)).mp
      (show 1-rho.re < 3/(40*Real.log x) by linarith)
    nlinarith only [hh]
  have hl := Real.log_le_log (by exact_mod_cast NeZero.pos q) hq
  rcases hbranch with ⟨h3, ht⟩ | ⟨h2, hi, ht⟩
  · have hu : 0 < (2/5)/Real.log x := by positivity
    have hu1 : (2/5)/Real.log x ≤ 1 := (div_le_one hL).mpr (by linarith)
    have hh := cubic_real_axis_single hc hp h3 (by linarith) hz
      (sigma := 1+(2/5)/Real.log x) (by linarith) (by linarith)
    have hinv : 1/(1+(2/5)/Real.log x-1)=(5/2)*Real.log x := by field_simp; ring
    rw [hinv] at hh
    exact coupled_kernel_contradiction hL (by norm_num : (0 : ℝ) < 2/5)
      (by norm_num : (0 : ℝ) < 3/40) (by norm_num : (0 : ℝ) ≤ 1/5)
      (by norm_num : (0 : ℝ) ≤ 7/2) hb hgap ht (by norm_num) (by norm_num) (by linarith)
  · have hu : 0 < 1/Real.log x := by positivity
    have hu1 : 1/Real.log x ≤ 1 := (div_le_one hL).mpr (by linarith)
    have hh := quadratic_real_axis_pair hc hp h2 (by linarith) hz hi
      (sigma := 1+1/Real.log x) (by linarith) (by linarith)
    have hinv : 1/(1+1/Real.log x-1)=Real.log x := by field_simp; ring
    rw [hinv] at hh
    exact coupled_kernel_contradiction hL (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 3/40) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (0 : ℝ) ≤ 3/2) hb hgap ht (by norm_num) (by norm_num) (by linarith)

theorem primitive_zero_real {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hz : chi.LFunction rho=0) : chi^2=1 ∧ rho.im=0 := by
  have hv : Real.log x*|rho.im| < 1/2 := by
    by_contra h
    exact primitive_scaled_high_no_zero hx hq hc hp hr ht (le_of_not_gt h) hz
  have hlow : chi^2=1 ∨ chi^3=1 := by
    by_contra h
    push Not at h
    exact primitive_other_orders_no_zero hx hq hc hp h.1 h.2 hr ht hz
  obtain h2 | h3 := hlow
  · refine ⟨h2, ?_⟩
    by_contra hi
    exact primitive_low_no_zero hx hq hc hp hr (Or.inr ⟨h2, hi, hv.le⟩) hz
  · have hv3 : Real.log x*|rho.im| < 1/5 := by
      by_contra h
      exact primitive_cubic_mid_no_zero hx hq hc hp h3 hr ht (le_of_not_gt h) hz
    exact False.elim (primitive_low_no_zero hx hq hc hp hr (Or.inl ⟨h3, hv3.le⟩) hz)

theorem ordinary_zero_real {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-3/(40*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hz : chi.LFunction rho=0) : chi^2=1 ∧ rho.im=0 := by
  have hhalf := region_re_half hx hr
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hc0 : (0 : ℝ) < chi.conductor := by exact_mod_cast NeZero.pos chi.conductor
  have ht' : |rho.im| ≤ x/(chi.conductor : ℝ) :=
    ht.trans (div_le_div_of_nonneg_left (by linarith) hc0 hcq)
  obtain ⟨h2, hi⟩ := primitive_zero_real hx (hcq.trans hq)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive hr ht'
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz)
  have hs : chi^2=1 := by
    by_contra h
    exact (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one chi h) h2
  exact ⟨hs, hi⟩

theorem zeta_no_zero {x : ℝ} (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x) : riemannZeta rho ≠ 0 := by
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hhalf := region_re_half hx hr
  intro hz
  obtain ⟨p, hv⟩ := exists_xi_index_of_zeta_zero (by linarith) hz
  have hb := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  have ht1 := xi_zero_height_gt_one p
  rw [hv] at hb ht1
  let u := (27/100)/Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by dsimp [u]; apply (div_le_iff₀ hL).mpr; linarith
  have huL : Real.log x*u=27/100 := by dsimp [u]; field_simp
  have hh := zeta_quartic_refined p (by rw [hv]; exact hhalf)
    (sigma := 1+u) (by linarith) (by linarith)
  rw [hv] at hh
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith : 0 < |rho.im|) ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hinv : 14379/(1+u-1)=(14379/(27/100))*Real.log x := by dsimp [u]; field_simp; ring
  rw [hinv] at hh
  have hupp : 24480/(1+u-rho.re) ≤
      (14379/(27/100)+46630*(691/2500)+1000)*Real.log x := by nlinarith only [hh, hl, hk, hlog]
  have hp := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 3/40 := by
    have hh := (lt_div_iff₀ (show 0 < 40*Real.log x by positivity)).mp
      (show 1-rho.re < 3/(40*Real.log x) by linarith)
    nlinarith only [hh]
  nlinarith only [hp, hgap, huL]

theorem principal_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ)) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  exact fun hz => zeta_no_zero hx hr (ht.trans (div_le_self (by linarith) hq))
    ((PrincipalPsi.principal_zero_iff_zeta_zero
      (by linarith [region_re_half hx hr]) hpole).mp hz)

theorem region_source_gap {x : ℝ} {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-3/(40*Real.log x) < rho.re) :
    1-rho.re < 1/(3*Real.log chi.conductor) := by
  have hl := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hc)
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hlog := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero) (hcq.trans hq)
  have hL : 0 < Real.log x := by linarith
  have hw : 3/(40*Real.log x) ≤ 1/(3*Real.log chi.conductor) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  linarith

theorem zero_real_quadratic_simple {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    exact principal_no_zero hx hr ht (hpole.resolve_left (by simp)) hz
  obtain ⟨hsq, hi⟩ := ordinary_zero_real hx hq chi hc hr ht hz
  exact ⟨hc, hsq, hi, real_zero_simple hc (by linarith [region_re_half hx hr])
    hz hi (region_source_gap hq chi hc hr)⟩

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation
