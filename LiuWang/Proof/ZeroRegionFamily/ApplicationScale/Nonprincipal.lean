import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.High

/-! # 应用尺度全部普通非主字符实性；复用已证真实低核 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale

theorem primitive_low_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 20 ≤ Real.log x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1-1/(14*Real.log x) < rho.re)
    (hbranch : (chi^3=1 ∧ Real.log x*|rho.im| ≤ 1/5) ∨
      (chi^2=1 ∧ rho.im ≠ 0 ∧ Real.log x*|rho.im| ≤ 1/2)) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
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
      (by norm_num : (0 : ℝ) < 1/14) (by norm_num : (0 : ℝ) ≤ 1/5)
      (by norm_num : (0 : ℝ) ≤ 7/2) hb hgap ht (by norm_num) (by norm_num) (by linarith)
  · have hu : 0 < 1/Real.log x := by positivity
    have hu1 : 1/Real.log x ≤ 1 := (div_le_one hL).mpr (by linarith)
    have hh := quadratic_real_axis_pair hc hp h2 (by linarith) hz hi
      (sigma := 1+1/Real.log x) (by linarith) (by linarith)
    have hinv : 1/(1+1/Real.log x-1)=Real.log x := by field_simp; ring
    rw [hinv] at hh
    exact coupled_kernel_contradiction hL (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/14) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (0 : ℝ) ≤ 3/2) hb hgap ht (by norm_num) (by norm_num) (by linarith)

theorem primitive_zero_real {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 20 ≤ Real.log x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1-1/(14*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
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
    (hx : 20 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hz : chi.LFunction rho=0) : chi^2=1 ∧ rho.im=0 := by
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hc0 : (0 : ℝ) < chi.conductor := by exact_mod_cast NeZero.pos chi.conductor
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
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

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale
