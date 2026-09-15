import LiuWang.Proof.MultiZeroRepulsion.Continuation.PrimitivePair
import LiuWang.Proof.MultiZeroRepulsion.ConjugateSlots

/-! Full closed-height exclusion for two primitive, nonprincipal, noninverse labels. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem conductorCoeff_le_691_2500 : stechkinConductorCoeff ≤ 691 / 2500 := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hk : 559 / 1250 ≤ stechkinK := by
    dsimp [stechkinK]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  dsimp [stechkinConductorCoeff]
  linarith

theorem source_log_lower {x : ℝ} (hx : 8000000000 ≤ x) : 9 / 2 ≤ Real.log x := by
  have ht := log_scale_ge (x := 10) le_rfl
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 2)
    (show (10 : ℝ) ^ 2 ≤ x by norm_num; linarith)
  rw [Real.log_pow] at hm
  norm_num at hm
  linarith

theorem ordinary_zero_order_pos {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (h1 : rho ≠ 1) (hz : chi.LFunction rho = 0) :
    0 < analyticOrderNatAt chi.LFunction rho := by
  apply Nat.pos_of_ne_zero
  intro he
  have hh := Nat.cast_analyticOrderNatAt (ordinary_order_ne_top chi h1)
  rw [he, Nat.cast_zero] at hh
  have hn := (ordinary_analytic chi h1).analyticOrderAt_eq_zero.mp hh.symm
  exact hn hz

theorem primitive_two_zero_exclusion {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    {chi psi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (hd : psi ≠ 1) (hpr : psi.IsPrimitive) (hm : chi * psi ≠ 1) (hi : chi * psi⁻¹ ≠ 1)
    {rho tau : ℂ}
    (hr : 1 - (2067 / 10000) / Real.log x < rho.re) (hr1 : rho.re < 1)
    (ht : 1 - (2067 / 10000) / Real.log x < tau.re) (ht1 : tau.re < 1)
    (hry : |rho.im| ≤ x / q) (hty : |tau.im| ≤ x / q)
    (hz : chi.LFunction rho = 0) (hw : psi.LFunction tau = 0) : False := by
  have hL := source_log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  let sigma := 1 + (499 / 1000) / Real.log x
  have hd0 : 0 < (499 / 1000 : ℝ) / Real.log x := by positivity
  have hds : (499 / 1000 : ℝ) / Real.log x ≤ 3 / 20 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hs : 1 < sigma := by dsimp [sigma]; linarith
  have hs1 : sigma ≤ 23 / 20 := by dsimp [sigma]; linarith
  have hwidth : (2067 / 10000 : ℝ) / Real.log x ≤ 1 / 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hrh : 1 / 2 < rho.re := by linarith
  have hth : 1 / 2 < tau.re := by linarith
  have hmr : (1 : ℝ) ≤ analyticOrderNatAt chi.LFunction rho := by
    exact_mod_cast ordinary_zero_order_pos chi (by intro h; simp [h] at hr1) hz
  have hmt : (1 : ℝ) ≤ analyticOrderNatAt psi.LFunction tau := by
    exact_mod_cast ordinary_zero_order_pos psi (by intro h; simp [h] at ht1) hw
  have hdenr : 0 < sigma - rho.re := by linarith
  have hdent : 0 < sigma - tau.re := by linarith
  have hmother := pair_primitive_global hq hc hp hd hpr hm hi hrh hr1 hth ht1 hry hty hs hs1
  have hselr := div_le_div_of_nonneg_right hmr hdenr.le
  have hselt := div_le_div_of_nonneg_right hmt hdent.le
  have hsL : (sigma - 1) * Real.log x = 499 / 1000 := by
    dsimp [sigma]
    field_simp
    ring
  have hbr : (1 - rho.re) * Real.log x < 2067 / 10000 := by
    apply (lt_div_iff₀ hL0).mp
    linarith
  have hbt : (1 - tau.re) * Real.log x < 2067 / 10000 := by
    apply (lt_div_iff₀ hL0).mp
    linarith
  have hlowr : Real.log x / (7057 / 10000) < 1 / (sigma - rho.re) := by
    apply (div_lt_div_iff₀ (by norm_num) hdenr).mpr
    nlinarith
  have hlowt : Real.log x / (7057 / 10000) < 1 / (sigma - tau.re) := by
    apply (div_lt_div_iff₀ (by norm_num) hdent).mpr
    nlinarith
  have hinv : 1 / (sigma - 1) = Real.log x / (499 / 1000) := by
    dsimp [sigma]
    field_simp
    ring
  rw [hinv] at hmother
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  norm_num [div_eq_mul_inv] at hmother hlowr hlowt hselr hselt hk
  nlinarith

theorem primitive_slots_same_or_inverse {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q))
    (hc : p.character ≠ 1) (hp : p.character.IsPrimitive)
    (hd : r.character ≠ 1) (hr : r.character.IsPrimitive) :
    p.character = r.character ∨ p.character = r.character⁻¹ := by
  by_contra hn
  have hm : p.character * r.character ≠ 1 := by
    intro he
    exact hn (Or.inr ((mul_eq_one_iff_eq_inv).mp he))
  have hi : p.character * r.character⁻¹ ≠ 1 := by
    intro he
    exact hn (Or.inl (by simpa using (mul_eq_one_iff_eq_inv).mp he))
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hw := mem_strictZeroValues.mp r.zero_mem
  exact primitive_two_zero_exclusion hx hq hc hp hd hr hm hi hz.2.2.1 hz.2.2.2.1
    hw.2.2.1 hw.2.2.2.1 hz.2.2.2.2 hw.2.2.2.2 hz.1 hw.1

end LiuWang.Proof.MultiZeroRepulsion.Continuation
