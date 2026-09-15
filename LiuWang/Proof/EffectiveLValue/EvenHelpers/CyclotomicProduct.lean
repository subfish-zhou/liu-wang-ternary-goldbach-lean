import LiuWang.Proof.EffectiveLValue.RealAbelLog

/-!
# The finite product attached to the actual real character

Integer exponents include the zero values of the character. In particular the
factor at zero is `0 ^ (0 : ℤ) = 1`, not a logarithmic singularity.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Complex Finset

variable {r : ℕ} [NeZero r]

def realCharacterSign (χ : Interfaces.Character r) (a : ZMod r) : ℤ :=
  if χ a = 1 then 1 else if χ a = -1 then -1 else 0

omit [NeZero r] in
theorem realCharacterSign_cast (χ : Interfaces.Character r) (hreal : χ ^ 2 = 1)
    (a : ZMod r) : (realCharacterSign χ a : ℂ) = χ a := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hreal a with h | h | h <;>
    norm_num [realCharacterSign, h]

theorem realCharacterSign_zero (χ : Interfaces.Character r) (hne : χ ≠ 1) :
    realCharacterSign χ 0 = 0 := by
  simp [realCharacterSign, realCharacter_zero χ hne]

theorem realCharacterSign_sum (χ : Interfaces.Character r) (hreal : χ ^ 2 = 1)
    (hne : χ ≠ 1) : ∑ a : ZMod r, realCharacterSign χ a = 0 := by
  apply Int.cast_injective (α := ℂ)
  push_cast
  simpa only [realCharacterSign_cast χ hreal] using χ.sum_eq_zero_of_ne_one hne

def characterCyclotomicProduct (χ : Interfaces.Character r) : ℂ :=
  ∏ a : ZMod r, (1 - ZMod.stdAddChar a) ^ realCharacterSign χ a

theorem stdAddChar_one_sub_ne_zero (a : ZMod r) (ha : a ≠ 0) :
    1 - ZMod.stdAddChar a ≠ 0 :=
  Complex.slitPlane_ne_zero (stdAddChar_sub_one_mem_slitPlane a ha)

theorem characterCyclotomicProduct_eq_exp (χ : Interfaces.Character r)
    (hreal : χ ^ 2 = 1) (hne : χ ≠ 1) :
    characterCyclotomicProduct χ =
      Complex.exp (∑ a : ZMod r, χ a * Complex.log (1 - ZMod.stdAddChar a)) := by
  rw [Complex.exp_sum]
  apply prod_congr rfl
  intro a _
  by_cases ha : a = 0
  · subst a
    simp [realCharacterSign_zero χ hne, realCharacter_zero χ hne]
  · rw [← realCharacterSign_cast χ hreal a, Complex.exp_int_mul,
      Complex.exp_log (stdAddChar_one_sub_ne_zero a ha)]

theorem characterCyclotomicProduct_eq_exp_LFunction (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (hne : χ ≠ 1) :
    characterCyclotomicProduct χ = Complex.exp (-(characterGaussSum χ * χ.LFunction 1)) := by
  rw [characterCyclotomicProduct_eq_exp χ hreal hne,
    realCharacter_gauss_mul_LFunction_one_log χ hprimitive hreal hne]
  congr 1
  simp only [mul_neg, sum_neg_distrib, neg_neg]

end LiuWang.Proof.EffectiveLValue
