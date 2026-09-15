import LiuWang.Proof.EffectiveLValue.RealAbelLog

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Complex Finset Filter Topology

variable {r : ℕ} [NeZero r]

omit [NeZero r] in
theorem oddCharacter_ne_one (χ : OddRealPrimitiveCharacter r) : χ.1 ≠ 1 := by
  intro h
  have ho := χ.2.2.2
  rw [DirichletCharacter.Odd, h,
    MulChar.one_apply (isUnit_one.neg)] at ho
  norm_num at ho

theorem oddCharacter_zero (χ : OddRealPrimitiveCharacter r) : χ.1 0 = 0 := by
  exact realCharacter_zero χ.1 (oddCharacter_ne_one χ)

theorem oddCharacter_gauss_fourier (χ : OddRealPrimitiveCharacter r) (n : ℕ) :
    characterGaussSum χ.1 * χ.1 n =
      ∑ a : ZMod r, χ.1 a * ZMod.stdAddChar a ^ n := by
  exact realCharacter_gauss_fourier χ.1 χ.2.1 χ.2.2.1 n

theorem oddCharacter_tendsto_abel (χ : OddRealPrimitiveCharacter r) :
    Tendsto (fun x : ℝ ↦ ∑' n : ℕ, (χ.1 n / n) * (x : ℂ) ^ n)
      (𝓝[<] 1) (𝓝 (χ.1.LFunction 1)) := by
  exact realCharacter_tendsto_abel χ.1 (oddCharacter_ne_one χ)

theorem oddCharacter_abel_log (χ : OddRealPrimitiveCharacter r) {x : ℝ}
    (hx : |x| < 1) :
    characterGaussSum χ.1 *
      (∑' n : ℕ, (χ.1 n / n) * (x : ℂ) ^ n) =
      ∑ a : ZMod r, χ.1 a * (-Complex.log (1 - x * ZMod.stdAddChar a)) := by
  exact realCharacter_abel_log χ.1 χ.2.1 χ.2.2.1 hx

theorem oddCharacter_gauss_mul_LFunction_one_log (χ : OddRealPrimitiveCharacter r) :
    characterGaussSum χ.1 * χ.1.LFunction 1 =
      ∑ a : ZMod r, χ.1 a * (-Complex.log (1 - ZMod.stdAddChar a)) := by
  exact realCharacter_gauss_mul_LFunction_one_log χ.1 χ.2.1 χ.2.2.1
    (oddCharacter_ne_one χ)

end LiuWang.Proof.EffectiveLValue
