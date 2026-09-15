import LiuWang.Proof.EffectiveLValue.OddHelpers.AbelLog

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Finset

variable {r : ℕ}

def oddCharacterInt (χ : OddRealPrimitiveCharacter r) (a : ZMod r) : ℤ :=
  if χ.1 a = 0 then 0 else if χ.1 a = 1 then 1 else -1

@[simp] theorem oddCharacterInt_cast (χ : OddRealPrimitiveCharacter r) (a : ZMod r) :
    (oddCharacterInt χ a : ℂ) = χ.1 a := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.2.2.1 a with h | h | h <;>
    norm_num [oddCharacterInt, h]

theorem oddCharacterInt_mul (χ : OddRealPrimitiveCharacter r) (a b : ZMod r) :
    oddCharacterInt χ (a * b) = oddCharacterInt χ a * oddCharacterInt χ b := by
  apply Int.cast_injective (α := ℂ)
  simp

@[simp] theorem oddCharacterInt_one (χ : OddRealPrimitiveCharacter r) :
    oddCharacterInt χ 1 = 1 := by
  apply Int.cast_injective (α := ℂ)
  simp

theorem oddCharacterInt_re (χ : OddRealPrimitiveCharacter r) (a : ZMod r) :
    (χ.1 a).re = oddCharacterInt χ a := by
  exact (show (oddCharacterInt χ a : ℝ) = (χ.1 a).re by
    simpa only [Complex.intCast_re] using congrArg Complex.re
      (oddCharacterInt_cast χ a)).symm

variable [NeZero r]

def oddCharacterMoment (χ : OddRealPrimitiveCharacter r) : ℤ :=
  ∑ a : ZMod r, oddCharacterInt χ a * (a.val : ℤ)

theorem oddCharacterInt_sum (χ : OddRealPrimitiveCharacter r) :
    ∑ a : ZMod r, oddCharacterInt χ a = 0 := by
  apply Int.cast_injective (α := ℂ)
  simpa using χ.1.sum_eq_zero_of_ne_one (oddCharacter_ne_one χ)

end LiuWang.Proof.EffectiveLValue
