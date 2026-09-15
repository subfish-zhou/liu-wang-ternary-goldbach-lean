import LiuWang.Proof.NonSymmetricContour.Rectangle
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Main

/-! # 在全部实端点之前固定分离高度，并复用水平边生产者 -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

namespace LiuWang.Proof.NonSymmetricContour

def AdmissibleHeights {q : Nat} [NeZero q] (N : Nat) (chi : Character q)
    (Hplus Hminus : Real) : Prop :=
  |Hplus - sourceT N| ≤ 1 ∧ |Hminus + sourceT N| ≤ 1 ∧
    ∀ p : CompletedZeroIndex chi,
      (1.7769 * Real.log ((q : Real) * sourceT N))⁻¹ ≤
        |(completedZeroValue p).im - Hplus| ∧
      (1.7769 * Real.log ((q : Real) * sourceT N))⁻¹ ≤
        |(completedZeroValue p).im - Hminus|

theorem sourceT_large {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    (2000 : Real) ^ (15 : Nat) ≤ sourceT N :=
  pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) _

theorem exists_admissibleHeights {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    ∃ Hplus Hminus, AdmissibleHeights N chi Hplus Hminus :=
  exists_source_rectangle_heights_index hq hchi hPrimitive (sourceT_large hN)

theorem admissibleHeights_signs {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) {chi : Character q} {Hplus Hminus : Real}
    (h : AdmissibleHeights N chi Hplus Hminus) :
    0 < Hplus ∧ Hminus < 0 := by
  have hT : 2 ≤ sourceT N := (by norm_num : (2 : Real) ≤ 2000 ^ (15 : Nat)).trans (sourceT_large hN)
  have hp := (abs_le.mp h.1).1
  have hm := (abs_le.mp h.2.1).2
  constructor <;> linarith

theorem admissibleHeights_line {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) {chi : Character q} {Hplus Hminus H : Real}
    (h : AdmissibleHeights N chi Hplus Hminus) (hH : H ∈ ({Hplus, Hminus} : Set Real)) :
    |(|H|) - sourceT N| ≤ 1 ∧ H ≠ 0 ∧
      ∀ p : CompletedZeroIndex chi, (1.7769 * Real.log ((q : Real) * sourceT N))⁻¹ ≤
        |(completedZeroValue p).im - H| := by
  obtain ⟨hp0, hm0⟩ := admissibleHeights_signs hN h
  rcases Set.mem_insert_iff.mp hH with rfl | hH
  · exact ⟨by simpa [abs_of_pos hp0] using h.1, hp0.ne', fun p => (h.2.2 p).1⟩
  · have he := Set.mem_singleton_iff.mp hH
    subst H
    refine ⟨?_, hm0.ne, fun p => (h.2.2 p).2⟩
    rw [abs_of_neg hm0, show -Hminus - sourceT N = -(Hminus + sourceT N) by ring, abs_neg]
    exact h.2.1

theorem admissibleHeights_border {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real} (h : AdmissibleHeights N chi Hplus Hminus) :
    ∀ s ∈ RectangleBorder (lowerLeft Hminus) (upperRight (1 + 1 / sourceL N) Hplus),
      chi.LFunction s ≠ 0 := by
  have hb : 1 ≤ 1 + 1 / sourceL N := by
    have hL := sourceL_pos hN
    have hi : 0 ≤ 1 / sourceL N := by positivity
    linarith
  obtain ⟨hp0, hm0⟩ := admissibleHeights_signs hN h
  apply LFunction_ne_zero_border hchi hPrimitive hb (by linarith)
  intro H hH σ hσ
  obtain ⟨_, hH0, hsep⟩ := admissibleHeights_line hN h hH
  exact LFunction_ne_zero_on_separated_strip hchi hPrimitive
    (source_height_budget_pos hq (sourceT_large hN)) hH0 hsep (by simp) (by simpa using hσ.1)

theorem admissibleHeights_horizontal_budget {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real} (h : AdmissibleHeights N chi Hplus Hminus)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    (∀ H ∈ ({Hplus, Hminus} : Set Real),
      IntervalIntegrable (fun σ : Real => horizontalIntegrand chi t
        ((σ : Complex) + (H : Complex) * Complex.I)) volume (-1 / 2) (1 + 1 / sourceL N)) ∧
    (‖horizontalIntegral (horizontalIntegrand chi t) (1 + 1 / sourceL N) Hplus‖ +
      ‖horizontalIntegral (horizontalIntegrand chi t) (1 + 1 / sourceL N) Hminus‖ ≤
        0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2) := by
  have ht0 : 0 < t := (sourceT_pos hN).trans (sourceT_lt_real_endpoint hN htlo)
  have hT0 := sourceT_pos hN
  have hB := source_height_budget_pos hq (sourceT_large hN)
  have hi : ∀ H ∈ ({Hplus, Hminus} : Set Real),
      ‖horizontalIntegral (horizontalIntegrand chi t) (1 + 1 / sourceL N) H‖ ≤
        ((21 / 5000 : Real) * t / sourceT N *
          (Real.log ((q : Real) * sourceT N)) ^ 2) / (2 * Real.pi) := by
    intro H hH
    obtain ⟨ha, _, hs⟩ := admissibleHeights_line hN h hH
    rw [norm_horizontalIntegral]
    exact div_le_div_of_nonneg_right
      (norm_horizontal_integral_source_sharp_le hN hq hchi hPrimitive htlo hthi ha hs)
      (by positivity)
  refine ⟨?_, ?_⟩
  · intro H hH
    obtain ⟨_, hH0, hs⟩ := admissibleHeights_line hN h hH
    apply ContinuousOn.intervalIntegrable_of_Icc
      (by
        have hL := sourceL_pos hN
        have hi : 0 ≤ 1 / sourceL N := by positivity
        linarith)
    exact continuousOn_horizontalIntegrand hchi hPrimitive ht0 hB hH0 hs
  · have hp := hi Hplus (by simp)
    have hm := hi Hminus (by simp)
    have hscale : 0 ≤ t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 := by positivity
    have hc : (21 / 2500 : Real) ≤ 0.0014 * (2 * Real.pi) := by linarith [Real.pi_gt_three]
    have hh := mul_le_mul_of_nonneg_right hc hscale
    calc
      _ ≤ _ := add_le_add hp hm
      _ ≤ _ := by
        rw [← add_div, div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
        convert hh using 1 <;> ring

end LiuWang.Proof.NonSymmetricContour
