import LiuWang.Proof.ExceptionalZeroGap.DerivativeScalar
import LiuWang.Proof.EffectiveLValue.Main
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDifferenceBound
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# 大导子实轴导数及给定局部实零点的距离

这是给定零点的局部估计，不断言零点存在、唯一或单根，也不选择全族例外。
导数界无需实性；实性仅用于调用已验的全奇偶 `L(1)` 下界。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ExceptionalZeroGap

open Complex

variable {r : ℕ} [NeZero r]

/-- 原文完整头尾的指数形式；允许所有 `σ ≥ nearOneLower x`。 -/
theorem norm_deriv_LFunction_le_source_bound {χ : Interfaces.Character r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {x σ y : ℝ}
    (hx : 10 ≤ x) (hσ : nearOneLower x ≤ σ) (hy : 10 ≤ y) :
    ‖deriv χ.LFunction (σ : ℂ)‖ ≤
      ((1 / 2) * (Real.log y) ^ 2 - (1 / 2) * (Real.log 3) ^ 2 +
        Real.log 3 / 3 + Real.log 2 / 2 +
        Real.sqrt r * Real.log r * Real.log y / y) *
          Real.exp (Real.log y / (9.645908801 * Real.log x)) := by
  have hτ1 : nearOneLower x ≤ 1 := by
    have hlog := two_le_log_of_ten_le hx
    unfold nearOneLower c1
    exact sub_le_self _ (by positivity)
  have h := norm_deriv_le_complete_head_tail_of_le hχ hr
    (half_le_nearOneLower hx) hτ1 hσ hy
  have hpow : y ^ (1 - nearOneLower x) =
      Real.exp (Real.log y / (9.645908801 * Real.log x)) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < y)]
    congr 1
    unfold nearOneLower c1
    ring
  simpa only [hpow, finiteHeadBudget] using h

theorem norm_deriv_LFunction_le {χ : Interfaces.Character r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {x σ : ℝ}
    (hx : 10 ≤ x) (hrx : (r : ℝ) ≤ x)
    (hσ0 : nearOneLower x ≤ σ) (hσ1 : σ ≤ 1) :
    ‖deriv χ.LFunction (σ : ℂ)‖ ≤ 0.4923 * (Real.log r) ^ 2 := by
  calc
    _ ≤ (finiteHeadBudget (13 * Real.sqrt r) +
        Real.sqrt r * Real.log r * Real.log (13 * Real.sqrt r) / (13 * Real.sqrt r)) *
          (13 * Real.sqrt r) ^ (1 - σ) :=
      norm_deriv_le_complete_head_tail hχ hr
        ((half_le_nearOneLower hx).trans hσ0) hσ1 (chosen_cutoff_ge_ten hr)
    _ ≤ (0.4497 * (Real.log r) ^ 2) * 1.0947 :=
      mul_le_mul (chosen_head_tail_coefficient_le hr) (chosen_power_le hr hx hrx hσ0)
        (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg (Real.log (r : ℝ))]

theorem real_zero_lt_one {χ : Interfaces.Character r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {β : ℝ}
    (hzero : χ.LFunction (β : ℂ) = 0) : β < 1 := by
  have hne := EffectiveLValue.primitiveCharacter_ne_one χ hχ (by omega : 1 < r)
  by_contra hβ
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hne)
    (show 1 ≤ (β : ℂ).re from le_of_not_gt hβ) hzero

theorem norm_LFunction_one_le_gap_mul {χ : Interfaces.Character r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {x β : ℝ}
    (hx : 10 ≤ x) (hrx : (r : ℝ) ≤ x) (hβ : nearOneLower x ≤ β)
    (hzero : χ.LFunction (β : ℂ) = 0) :
    ‖χ.LFunction 1‖ ≤ 0.4923 * (Real.log r) ^ 2 * (1 - β) := by
  have hne := EffectiveLValue.primitiveCharacter_ne_one χ hχ (by omega : 1 < r)
  have hβ1 := real_zero_lt_one hχ hr hzero
  have hint : (∫ σ in β..1, deriv χ.LFunction (σ : ℂ)) = χ.LFunction 1 := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one, hzero, sub_zero] using
      DirichletLWeakStripDifferenceBound.integral_deriv_LFunction_eq_sub χ hne β 1 0
  rw [← hint]
  have hbound : ∀ σ ∈ Set.uIoc β 1,
      ‖deriv χ.LFunction (σ : ℂ)‖ ≤ 0.4923 * (Real.log r) ^ 2 := by
    intro σ hσ
    rw [Set.uIoc_of_le hβ1.le] at hσ
    exact norm_deriv_LFunction_le hχ hr hx hrx (hβ.trans hσ.1.le) hσ.2
  simpa only [abs_of_nonneg (sub_nonneg.mpr hβ1.le)] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- 原域和原常数下，已经给定的局部实零点的距离下界。 -/
theorem real_primitive_local_zero_gap {χ : Interfaces.Character r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r)
    (hreal : ∀ a : ZMod r, (χ a).im = 0) {x β : ℝ}
    (hx : 10 ≤ x) (hrx : (r : ℝ) ≤ x) (hβ : nearOneLower x ≤ β)
    (hzero : χ.LFunction (β : ℂ) = 0) :
    Real.pi / (0.4923 * Real.sqrt r * (Real.log r) ^ 2) ≤ 1 - β := by
  have hL := EffectiveLValue.real_primitive_LFunction_one_lower χ hr hχ hreal
  have hupper := norm_LFunction_one_le_gap_mul hχ hr hx hrx hβ hzero
  have hpaid := hL.trans ((Complex.re_le_norm _).trans hupper)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs := Real.sqrt_pos.2 hr0
  have hlog : 0 < Real.log (r : ℝ) := by linarith [log_large_conductor_lower hr]
  apply (div_le_iff₀ (by positivity : 0 < 0.4923 * Real.sqrt r * (Real.log r) ^ 2)).2
  have h := (div_le_iff₀ hs).1 hpaid
  nlinarith only [h]

end LiuWang.Proof.ExceptionalZeroGap
