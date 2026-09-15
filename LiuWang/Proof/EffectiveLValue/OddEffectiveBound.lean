import LiuWang.Proof.EffectiveLValue.OddValueFormula
import LiuWang.Proof.EffectiveLValue.OddHelpers.IntegralMoment

/-!
实际奇本原实字符的显式下界。有限和公式保留导子分母，随后由实际整除性及
非零性证明归一化绝对值为正整数；此处不使用导子—判别式或 Dedekind ζ 分解。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

variable {r : ℕ} [NeZero r]

theorem oddCharacterMoment_normalized_pos_integer (χ : OddRealPrimitiveCharacter r)
    (hr : 8 < r) :
    ∃ k : ℕ, 1 ≤ k ∧ |(oddCharacterMoment χ : ℝ)| / r = k := by
  obtain ⟨z, hz⟩ := oddCharacterMoment_dvd χ hr
  have hz0 : z ≠ 0 := by
    intro h
    apply oddCharacterMoment_ne_zero χ (by omega)
    rw [hz, h, mul_zero]
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz0, ?_⟩
  have hrpos : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  rw [hz, Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_pos hrpos,
    mul_div_cancel_left₀ _ hrpos.ne']
  simpa only [Int.cast_abs] using (Nat.cast_natAbs (α := ℝ) z).symm

theorem oddCharacter_LFunction_one_pos_integer_multiple (χ : OddRealPrimitiveCharacter r)
    (hr : 8 < r) :
    ∃ k : ℕ, 1 ≤ k ∧
      (χ.1.LFunction 1).re = (Real.pi / Real.sqrt (r : ℝ)) * k := by
  obtain ⟨k, hk, he⟩ := oddCharacterMoment_normalized_pos_integer χ hr
  refine ⟨k, hk, ?_⟩
  rw [oddCharacter_LFunction_one_formula χ (by omega), he]

theorem oddCharacter_LFunction_one_lower (χ : OddRealPrimitiveCharacter r)
    (hr : 8 < r) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.1.LFunction 1).re := by
  obtain ⟨k, hk, he⟩ := oddCharacter_LFunction_one_pos_integer_multiple χ hr
  rw [he]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hk'
    (by positivity : 0 ≤ Real.pi / Real.sqrt (r : ℝ))

theorem odd_real_primitive_LFunction_one_lower (χ : Interfaces.Character r)
    (hr : 987 ≤ r) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod r, (χ a).im = 0) (hodd : χ.Odd) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.LFunction 1).re := by
  exact oddCharacter_LFunction_one_lower
    ⟨χ, hprimitive, (character_sq_eq_one_iff_real χ).mpr hreal, hodd⟩ (by omega)

end LiuWang.Proof.EffectiveLValue
