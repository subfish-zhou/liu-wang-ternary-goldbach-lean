import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.High
import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Cubic

/-! # 实际二/三阶低高度付款及完整R14非主实性 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem coupled_kernel_contradiction {L A b v C beta gamma : ℝ}
    (hL : 0 < L) (hA : 0 < A) (hb : 0 < b) (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hbeta : beta < 1) (hgap : (1-beta)*L < b) (ht : L*|gamma| ≤ v)
    (hleft : C*(A^2+v^2) < 2*A)
    (hright : C*((A+b)^2+v^2) < 2*(A+b))
    (hkernel : 2*(1+A/L-beta)/((1+A/L-beta)^2+gamma^2) ≤ C*L) : False := by
  have hu : 0 < A/L := div_pos hA hL
  have huL : L*(A/L)=A := by field_simp
  have hd : 0 < (1+A/L-beta)^2+gamma^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith)) (sq_nonneg _)
  have hp := (div_le_iff₀ hd).mp hkernel
  have hm := mul_le_mul_of_nonneg_left hp hL.le
  let d := L*(1+A/L-beta)
  have hdA : A ≤ d := by dsimp [d]; nlinarith
  have hdB : d ≤ A+b := by dsimp [d]; nlinarith
  have htsq : L^2*gamma^2 ≤ v^2 := by
    nlinarith [sq_abs gamma, mul_nonneg (show 0 ≤ v-L*|gamma| by linarith)
      (show 0 ≤ v+L*|gamma| by positivity)]
  have hpaid : 2*d ≤ C*(d^2+v^2) := by
    dsimp [d]
    nlinarith [mul_le_mul_of_nonneg_left htsq hC]
  have hchord := mul_nonneg (show 0 ≤ d-A by linarith) (show 0 ≤ A+b-d by linarith)
  have h1 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ A+b-d by linarith)
    (show C*(A^2+v^2)-2*A ≤ 0 by linarith)
  by_cases he : d=A
  · rw [he] at hpaid
    linarith
  · have h2s := mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_le_of_ne hdA (Ne.symm he)))
      (show C*((A+b)^2+v^2)-2*(A+b) < 0 by linarith)
    nlinarith only [h1, h2s, mul_nonneg hb.le (sub_nonneg.mpr hpaid),
      mul_nonneg (mul_nonneg hb.le hC) hchord]

theorem primitive_cubic_low_no_zero_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (h3 : chi^3=1)
    {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : Real.log x*|rho.im| ≤ 1/5) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hu : 0 < (2/5)/Real.log x := by positivity
  have hu1 : (2/5)/Real.log x ≤ 1 := (div_le_one hL).mpr (by linarith)
  have hh := cubic_real_axis_single hc hp h3 (by linarith) hz
    (sigma := 1+(2/5)/Real.log x) (by linarith) (by linarith)
  have hinv : 1/(1+(2/5)/Real.log x-1)=(5/2)*Real.log x := by field_simp; ring
  rw [hinv] at hh
  have hl := Real.log_le_log (by exact_mod_cast NeZero.pos q) hq
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
    nlinarith only [hh]
  exact coupled_kernel_contradiction hL (by norm_num : (0 : ℝ) < 2/5)
    (by norm_num : (0 : ℝ) < 1/14) (by norm_num : (0 : ℝ) ≤ 1/5)
    (by norm_num : (0 : ℝ) ≤ 7/2) hb hgap ht (by norm_num) (by norm_num)
    (by linarith)

theorem primitive_quadratic_low_no_zero_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (h2 : chi^2=1)
    {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re) (hi : rho.im ≠ 0)
    (ht : Real.log x*|rho.im| ≤ 1/2) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hu : 0 < 1/Real.log x := by positivity
  have hu1 : 1/Real.log x ≤ 1 := (div_le_one hL).mpr (by linarith)
  have hh := quadratic_real_axis_pair hc hp h2 (by linarith) hz hi
    (sigma := 1+1/Real.log x) (by linarith) (by linarith)
  have hinv : 1/(1+1/Real.log x-1)=Real.log x := by field_simp; ring
  rw [hinv] at hh
  have hl := Real.log_le_log (by exact_mod_cast NeZero.pos q) hq
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
    nlinarith only [hh]
  exact coupled_kernel_contradiction hL (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1/14) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 3/2) hb hgap ht (by norm_num) (by norm_num)
    (by linarith)

theorem ordinary_zero_real_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hr : 1-1/(14*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hz : chi.LFunction rho=0) : chi^2=1 ∧ rho.im=0 := by
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hzp := primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz
  have hv : Real.log x*|rho.im| < 1/2 := by
    by_contra h
    exact scaled_high_no_zero_fourteen hx hq chi hc hr ht (le_of_not_gt h) hz
  have hlow : chi^2=1 ∨ chi^3=1 := by
    by_contra h
    push Not at h
    exact powers_two_three_no_zero_fourteen_refined hx hq chi hc h.1 h.2 hr ht hz
  obtain h2 | h3 := hlow
  · refine ⟨h2, ?_⟩
    by_contra hi
    exact primitive_quadratic_low_no_zero_fourteen hx (hcq.trans hq) hpr
      chi.primitiveCharacter_isPrimitive
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi h2)
      hr hi hv.le hzp
  · have hv3 : Real.log x*|rho.im| < 1/5 := by
      by_contra h
      exact cubic_scaled_high_no_zero_fourteen hx hq chi hc h3 hr ht (le_of_not_gt h) hz
    exact False.elim (primitive_cubic_low_no_zero_fourteen hx (hcq.trans hq) hpr
      chi.primitiveCharacter_isPrimitive
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi h3)
      hr hv3.le hzp)

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
