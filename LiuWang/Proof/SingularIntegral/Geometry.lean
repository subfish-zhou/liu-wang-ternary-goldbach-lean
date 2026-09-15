import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# 原文 (4.3) 的实际截断单纯形

所有小数均为精确有理数；第三坐标始终为 `1 - x₁ - x₂`。
二维换元分解为两次区间换元，不引入频率变量的 Fubini。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Interval

namespace LiuWang.Proof.SingularIntegral

def sourceSimplex : Set (ℝ × ℝ) :=
  {x | 0.001 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0.001 ≤ x.2 ∧ x.2 ≤ 1 ∧
    0.001 ≤ 1 - x.1 - x.2 ∧ 1 - x.1 - x.2 ≤ 1}

def triangle : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc 0.001 0.998 ∧ x.2 ∈ Icc 0.001 (0.999 - x.1)}

theorem sourceSimplex_eq_triangle : sourceSimplex = triangle := by
  ext x
  simp only [sourceSimplex, triangle, mem_ofPred_eq, mem_Icc]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨⟨h₁, by linarith⟩, h₃, by linarith⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨h₁, by linarith, h₃, by linarith, by linarith, by linarith⟩

theorem mem_sourceSimplex_iff_coordinates (x₁ x₂ x₃ : ℝ)
    (hsum : x₁ + x₂ + x₃ = 1) :
    (x₁, x₂) ∈ sourceSimplex ↔
      x₁ ∈ Icc 0.001 1 ∧ x₂ ∈ Icc 0.001 1 ∧ x₃ ∈ Icc 0.001 1 := by
  have hx₃ : x₃ = 1 - x₁ - x₂ := by linarith
  subst x₃
  simp only [sourceSimplex, mem_ofPred_eq, mem_Icc]
  tauto

theorem triangle_isCompact : IsCompact triangle := by
  have hc : IsClosed triangle := by
    change IsClosed {x : ℝ × ℝ |
      (0.001 ≤ x.1 ∧ x.1 ≤ 0.998) ∧ (0.001 ≤ x.2 ∧ x.2 ≤ 0.999 - x.1)}
    exact ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd (continuous_const.sub continuous_fst)))
  refine ((isCompact_Icc : IsCompact (Icc (0.001 : ℝ) 0.998)).prod
    (isCompact_Icc : IsCompact (Icc (0.001 : ℝ) 0.998))).of_isClosed_subset hc ?_
  intro x hx
  change x.1 ∈ Icc (0.001 : ℝ) 0.998 ∧ x.2 ∈ Icc (0.001 : ℝ) 0.998
  exact ⟨hx.1, hx.2.1, by linarith [hx.1.1, hx.2.2]⟩

theorem triangle_measurableSet : MeasurableSet triangle :=
  triangle_isCompact.isClosed.measurableSet

theorem triangle_iterated_area :
    (∫ x₁ in (0.001 : ℝ)..0.998, ∫ _x₂ in (0.001 : ℝ)..(0.999 - x₁),
      (1 : ℝ)) = 0.997 ^ 2 / 2 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hi : (∫ x in (0.001 : ℝ)..0.998, (0.999 - x) - 0.001) =
      ∫ x in (0.001 : ℝ)..0.998, 0.998 - x := by
    congr 1
    ext x
    ring
  rw [hi, intervalIntegral.integral_sub
    (f := fun _ : ℝ => (0.998 : ℝ)) (g := fun x : ℝ => x)
    (intervalIntegrable_const) (continuous_id.intervalIntegrable _ _)]
  norm_num [integral_id]

theorem triangle_iterated_area_complex :
    (∫ x₁ in (0.001 : ℝ)..0.998, ∫ _x₂ in (0.001 : ℝ)..(0.999 - x₁),
      (1 : ℂ)) = (0.997 : ℂ) ^ 2 / 2 := by
  have h := congrArg Complex.ofReal triangle_iterated_area
  push_cast at h
  simpa only [← intervalIntegral.integral_ofReal, Complex.ofReal_one] using h

theorem triangle_two_dimensional_scaling (N : ℝ) (f : ℝ → ℝ → ℂ) :
    (∫ t₁ in (N * 0.001)..(N * 0.998),
      ∫ t₂ in (N * 0.001)..(N * (0.999 - t₁ / N)), f t₁ t₂) =
    (N : ℂ) ^ 2 * (∫ x₁ in (0.001 : ℝ)..0.998,
      ∫ x₂ in (0.001 : ℝ)..(0.999 - x₁), f (N * x₁) (N * x₂)) := by
  by_cases hN : N = 0
  · simp [hN]
  rw [← intervalIntegral.smul_integral_comp_mul_left]
  simp only [mul_div_cancel_left₀ _ hN]
  simp_rw [← intervalIntegral.smul_integral_comp_mul_left]
  rw [intervalIntegral.integral_smul]
  simp only [Complex.real_smul]
  ring

end LiuWang.Proof.SingularIntegral
