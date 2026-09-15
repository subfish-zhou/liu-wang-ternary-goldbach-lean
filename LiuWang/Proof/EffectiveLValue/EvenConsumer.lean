import LiuWang.Proof.EffectiveLValue.EvenHelpers.ProductPell

/-!
# Original-domain consumers of the even prefix

These statements use the requested actual character, without primality or a
fixed conductor. They deliberately do not assert the unfinished lower bound.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue.EvenConsumer

variable {r : ℕ} [NeZero r]

theorem actual_even_logarithm (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (heven : χ.Even) :
    Real.log (evenCharacterLargeProduct χ) =
      Real.sqrt (r : ℝ) * (χ.LFunction 1).re :=
  evenCharacterLargeProduct_log χ hprimitive ((character_sq_eq_one_iff_real χ).mpr hreal)
    heven (by omega)

theorem actual_even_integral_product (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (heven : χ.Even) :
    IsIntegral ℤ (characterCyclotomicProduct χ) ∧
      IsIntegral ℤ (characterCyclotomicProduct χ)⁻¹ ∧
      0 < (characterCyclotomicProduct χ).re ∧
      (characterCyclotomicProduct χ).im = 0 ∧ characterCyclotomicProduct χ ≠ 1 := by
  have hs := (character_sq_eq_one_iff_real χ).mpr hreal
  have hr1 : 1 < r := by omega
  have hn := primitiveCharacter_ne_one χ hprimitive hr1
  exact ⟨characterCyclotomicProduct_isIntegral χ hs hn hr1,
    characterCyclotomicProduct_inv_isIntegral χ hs hn hr1,
    evenCharacter_product_pos χ hprimitive hs heven hr1,
    evenCharacter_product_im χ hprimitive hs heven hr1,
    evenCharacter_product_ne_one χ hprimitive hs heven hr1⟩

theorem actual_even_pell_prefix (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (heven : χ.Even) :
    1 < evenCharacterLargeProduct χ ∧
      ∃ (v : ℤ) (q : ℚ), 0 < v ∧ 0 < q ∧
        (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4 ∧
        evenCharacterLargeProduct χ = ((v : ℝ) + (q : ℝ) * Real.sqrt (r : ℝ)) / 2 := by
  have hs := (character_sq_eq_one_iff_real χ).mpr hreal
  have hr1 : 1 < r := by omega
  exact ⟨evenCharacterLargeProduct_gt_one χ hprimitive hs heven hr1,
    evenCharacterLargeProduct_pell_rat χ hprimitive hs heven hr1⟩

theorem cutoff_987_pell_prefix (χ : Interfaces.Character 987) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod 987, (χ a).im = 0) (heven : χ.Even) :
    1 < evenCharacterLargeProduct χ ∧
      ∃ (v : ℤ) (q : ℚ), 0 < v ∧ 0 < q ∧
        (v : ℝ) ^ 2 - 987 * (q : ℝ) ^ 2 = 4 ∧
        evenCharacterLargeProduct χ = ((v : ℝ) + (q : ℝ) * Real.sqrt 987) / 2 := by
  simpa using actual_even_pell_prefix χ (by norm_num) hprimitive hreal heven

end LiuWang.Proof.EffectiveLValue.EvenConsumer
