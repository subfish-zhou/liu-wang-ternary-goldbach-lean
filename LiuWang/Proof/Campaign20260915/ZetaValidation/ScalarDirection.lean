import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
Algebraic checks for the SOURCE_CHECK at Liu--Wang, Acta Arith. 102 (2002),
page 269, (2.29). These do not replace the printed inequality or construct
zeros of an L-function. The existing CountCap proof from (2.28) is unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem max_lower_bound_of_reciprocal_sum {a B b₁ b₂ b₃ : ℝ}
    (ha : 0 < a) (hB : 0 < B)
    (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ b₂) (h₃ : 0 ≤ b₃)
    (h : 0 ≤ 1 / a -
      (1 / (a + b₁) + 1 / (a + b₂) + 1 / (a + b₃)) + B) :
    3 / (1 / a + B) - a ≤ max b₁ (max b₂ b₃) := by
  let m := max b₁ (max b₂ b₃)
  have hm₁ : b₁ ≤ m := le_max_left _ _
  have hm₂ : b₂ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm₃ : b₃ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have ham : 0 < a + m :=
    lt_of_lt_of_le (add_pos_of_pos_of_nonneg ha h₁) (add_le_add le_rfl hm₁)
  have hr₁ := one_div_le_one_div_of_le
    (add_pos_of_pos_of_nonneg ha h₁) (add_le_add le_rfl hm₁)
  have hr₂ := one_div_le_one_div_of_le
    (add_pos_of_pos_of_nonneg ha h₂) (add_le_add le_rfl hm₂)
  have hr₃ := one_div_le_one_div_of_le
    (add_pos_of_pos_of_nonneg ha h₃) (add_le_add le_rfl hm₃)
  have hs : 3 / (a + m) ≤ 1 / a + B := by
    rw [div_eq_mul_one_div]
    linarith only [h, hr₁, hr₂, hr₃]
  have hD : 0 < 1 / a + B := by positivity
  have hp := (div_le_iff₀ ham).mp hs
  have hq : 3 / (1 / a + B) ≤ a + m :=
    (div_le_iff₀ hD).mpr (by nlinarith only [hp])
  change 3 / (1 / a + B) - a ≤ m
  linarith only [hq]

theorem scalar_printed_direction_counterexample :
    ∃ a B b₁ b₂ b₃ : ℝ,
      0 < a ∧ a ≤ 0.3784 ∧ 0 < B ∧
      (0 ≤ b₁ ∧ b₁ ≤ a) ∧ (0 ≤ b₂ ∧ b₂ ≤ a) ∧ (0 ≤ b₃ ∧ b₃ ≤ a) ∧
      0 ≤ 1 / a - (1 / (a + b₁) + 1 / (a + b₂) + 1 / (a + b₃)) + B ∧
      ¬max b₁ (max b₂ b₃) ≤ 3 / (1 / a + B) - a := by
  refine ⟨1 / 3, 2, 1 / 3, 1 / 3, 1 / 3, ?_⟩
  norm_num

theorem optimal_choice_scalar_counterexample {B : ℝ} (hB : 0 < B) :
    let a := (Real.sqrt 3 - 1) / B
    0 < a ∧
      0 ≤ 1 / a - (1 / (a + a) + 1 / (a + a) + 1 / (a + a)) + B ∧
      ¬max a (max a a) ≤ 3 / (1 / a + B) - a := by
  let a := (Real.sqrt 3 - 1) / B
  have hr : (3 / 2 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have ha : 0 < a := div_pos (by linarith) hB
  have hab : a * B = Real.sqrt 3 - 1 := div_mul_cancel₀ _ hB.ne'
  have hid :
      1 / a - (1 / (a + a) + 1 / (a + a) + 1 / (a + a)) + B =
        (2 * (a * B) - 1) / (2 * a) := by
    field_simp
    ring
  have hD : 0 < 1 / a + B := by positivity
  have haD : a * (1 / a + B) = Real.sqrt 3 := by
    calc
      _ = 1 + a * B := by field_simp
      _ = _ := by rw [hab]; ring
  change 0 < a ∧ _ ∧ _
  refine ⟨ha, ?_, ?_⟩
  · rw [hid]
    exact div_nonneg (by nlinarith only [hab, hr]) (by positivity)
  · simp only [max_self, not_le]
    apply sub_lt_iff_lt_add.mpr
    apply (div_lt_iff₀ hD).mpr
    nlinarith only [haD, hr]

#print axioms max_lower_bound_of_reciprocal_sum
#print axioms scalar_printed_direction_counterexample
#print axioms optimal_choice_scalar_counterexample

end LiuWang.Proof.Campaign20260915.ZetaValidation
