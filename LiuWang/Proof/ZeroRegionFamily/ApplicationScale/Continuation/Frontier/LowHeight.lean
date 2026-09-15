import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.RealFamily

/-! # 原常数更宽的真实低高度二/三阶排除：普通非本原运输

完整区域仍须支付互补高度；这里不假设原区域所有字符属于低阶分支。
-/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.LowOrderClosure (cubic_real_axis_single coupled_kernel_contradiction)

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

theorem primitive_low_height_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1-21/(200*Real.log x) < rho.re)
    (hbranch : (chi^3=1 ∧ Real.log x*|rho.im| ≤ 1/6) ∨
      (chi^2=1 ∧ rho.im ≠ 0 ∧ Real.log x*|rho.im| ≤ 1/2)) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith
  have hw : 21/(200*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hgap : (1-rho.re)*Real.log x < 21/200 := by
    have hh := (lt_div_iff₀ (show 0 < 200*Real.log x by positivity)).mp
      (show 1-rho.re < 21/(200*Real.log x) by linarith)
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
      (by norm_num : (0 : ℝ) < 21/200) (by norm_num : (0 : ℝ) ≤ 1/6)
      (by norm_num : (0 : ℝ) ≤ 7/2) hb hgap ht (by norm_num) (by norm_num) (by linarith)
  · have hu : 0 < 1/Real.log x := by positivity
    have hu1 : 1/Real.log x ≤ 1 := (div_le_one hL).mpr (by linarith)
    have hh := quadratic_real_axis_pair hc hp h2 (by linarith) hz hi
      (sigma := 1+1/Real.log x) (by linarith) (by linarith)
    have hinv : 1/(1+1/Real.log x-1)=Real.log x := by field_simp; ring
    rw [hinv] at hh
    exact coupled_kernel_contradiction hL (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 21/200) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (0 : ℝ) ≤ 3/2) hb hgap ht (by norm_num) (by norm_num) (by linarith)

theorem ordinary_low_height_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : 1-21/(200*Real.log x) < rho.re)
    (hbranch : (chi^3=1 ∧ Real.log x*|rho.im| ≤ 1/6) ∨
      (chi^2=1 ∧ rho.im ≠ 0 ∧ Real.log x*|rho.im| ≤ 1/2)) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hlog := log_scale_ge_34_15 hx
  have hw : 21/(200*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  apply primitive_low_height_no_zero hx (hcq.trans hq)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive hr _ (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc
      (by linarith) hz)
  rcases hbranch with ⟨h3, ht⟩ | ⟨h2, hi, ht⟩
  · exact Or.inl ⟨BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi h3, ht⟩
  · exact Or.inr ⟨BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi h2, hi, ht⟩

theorem ordinary_low_height_original {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : 1-1/(9.645908801*Real.log x) < rho.re)
    (hbranch : (chi^3=1 ∧ Real.log x*|rho.im| ≤ 1/6) ∨
      (chi^2=1 ∧ rho.im ≠ 0 ∧ Real.log x*|rho.im| ≤ 1/2)) : chi.LFunction rho ≠ 0 := by
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hw : 1/(9.645908801*Real.log x) ≤ 21/(200*Real.log x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  exact ordinary_low_height_no_zero hx hq chi hc (by linarith) hbranch

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
