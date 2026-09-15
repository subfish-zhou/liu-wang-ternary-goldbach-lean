import LiuWang.Proof.EffectiveLValue.EvenHelpers.CyclotomicProduct
import Mathlib.Algebra.Ring.GeomSum

/-!
# Integrality of the actual finite cyclotomic product and its inverse

Normalization by `1 - stdAddChar 1` is justified by the zero character sum.
Each normalized factor at a unit, and its inverse, is a geometric sum of
roots of unity. Neither a class number formula nor a regulator is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Complex Finset

variable {r : ℕ} [NeZero r]

theorem stdAddChar_isIntegral (a : ZMod r) : IsIntegral ℤ (ZMod.stdAddChar a) := by
  apply IsIntegral.of_pow (n := r) (NeZero.pos r)
  have h : ZMod.stdAddChar a ^ r = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      AddChar.map_zero_eq_one]
  rw [h]
  exact isIntegral_one

theorem stdAddChar_pow_val_mul (a b : ZMod r) :
    ZMod.stdAddChar b ^ a.val = ZMod.stdAddChar (a * b) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem stdAddChar_ratio_eq_geom_sum (a : ZMod r) (b : (ZMod r)ˣ) (hr : 1 < r) :
    (1 - ZMod.stdAddChar a) / (1 - ZMod.stdAddChar (b : ZMod r)) =
      ∑ k ∈ range (a * ↑b⁻¹ : ZMod r).val, ZMod.stdAddChar (b : ZMod r) ^ k := by
  let : Fact (1 < r) := ⟨hr⟩
  apply (div_eq_iff (stdAddChar_one_sub_ne_zero _ b.ne_zero)).mpr
  rw [geom_sum_mul_neg, stdAddChar_pow_val_mul]
  simp only [mul_assoc, Units.inv_mul, mul_one]

theorem stdAddChar_ratio_isIntegral (a : ZMod r) (b : (ZMod r)ˣ) (hr : 1 < r) :
    IsIntegral ℤ ((1 - ZMod.stdAddChar a) / (1 - ZMod.stdAddChar (b : ZMod r))) := by
  rw [stdAddChar_ratio_eq_geom_sum a b hr]
  exact IsIntegral.sum _ (fun k _ ↦ (stdAddChar_isIntegral _).pow k)

theorem characterCyclotomicProduct_eq_normalized (χ : Interfaces.Character r)
    (hreal : χ ^ 2 = 1) (hne : χ ≠ 1) (hr : 1 < r) :
    characterCyclotomicProduct χ =
      ∏ a : ZMod r,
        ((1 - ZMod.stdAddChar a) / (1 - ZMod.stdAddChar (1 : ZMod r))) ^
          realCharacterSign χ a := by
  let : Fact (1 < r) := ⟨hr⟩
  have hb := stdAddChar_one_sub_ne_zero (1 : ZMod r) one_ne_zero
  have hp (s : Finset (ZMod r)) :
      ∏ a ∈ s, (1 - ZMod.stdAddChar (1 : ZMod r)) ^ realCharacterSign χ a =
        (1 - ZMod.stdAddChar (1 : ZMod r)) ^ (∑ a ∈ s, realCharacterSign χ a) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, zpow_add₀ hb]
  simp only [div_zpow, prod_div_distrib, hp, realCharacterSign_sum χ hreal hne,
    zpow_zero, div_one, characterCyclotomicProduct]

theorem characterCyclotomicProduct_isIntegral (χ : Interfaces.Character r)
    (hreal : χ ^ 2 = 1) (hne : χ ≠ 1) (hr : 1 < r) :
    IsIntegral ℤ (characterCyclotomicProduct χ) := by
  rw [characterCyclotomicProduct_eq_normalized χ hreal hne hr]
  apply IsIntegral.prod
  intro a _
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hreal (u : ZMod r) with h | h | h
    · exact False.elim ((MulChar.apply_ne_zero_iff.mpr u.isUnit) h)
    · simpa [realCharacterSign, h] using stdAddChar_ratio_isIntegral (u : ZMod r) 1 hr
    · have hs : realCharacterSign χ (u : ZMod r) = -1 := by
        norm_num [realCharacterSign, h]
      simpa only [hs, zpow_neg_one, inv_div, Units.val_one] using
        stdAddChar_ratio_isIntegral 1 u hr
  · have hz := χ.map_nonunit ha
    simp [realCharacterSign, hz, isIntegral_one]

theorem characterCyclotomicProduct_inv_isIntegral (χ : Interfaces.Character r)
    (hreal : χ ^ 2 = 1) (hne : χ ≠ 1) (hr : 1 < r) :
    IsIntegral ℤ (characterCyclotomicProduct χ)⁻¹ := by
  rw [characterCyclotomicProduct_eq_normalized χ hreal hne hr, ← prod_inv_distrib]
  apply IsIntegral.prod
  intro a _
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hreal (u : ZMod r) with h | h | h
    · exact False.elim ((MulChar.apply_ne_zero_iff.mpr u.isUnit) h)
    · simpa [realCharacterSign, h, inv_div] using stdAddChar_ratio_isIntegral 1 u hr
    · have hs : realCharacterSign χ (u : ZMod r) = -1 := by
        norm_num [realCharacterSign, h]
      simpa only [hs, zpow_neg_one, inv_inv, Units.val_one] using
        stdAddChar_ratio_isIntegral (u : ZMod r) 1 hr
  · have hz := χ.map_nonunit ha
    simp [realCharacterSign, hz, isIntegral_one]

end LiuWang.Proof.EffectiveLValue
