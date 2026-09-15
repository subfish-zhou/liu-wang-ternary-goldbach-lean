import LiuWang.Proof.EffectiveLValue.EvenHelpers.CyclotomicProduct
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticValueAtOnePositive

/-!
# The even real primitive character's actual logarithmic value

The Gauss sum need not be assigned a sign: its absolute real part is `sqrt r`.
The product below is the finite cyclotomic product, not a freely chosen unit.
Its positivity and nontriviality follow from the exact Abel identity.
This file does not claim the quantitative gap required by (2.36).
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Complex Finset

variable {r : ℕ} [NeZero r]

theorem even_characterGaussSum_im (χ : Interfaces.Character r)
    (hreal : χ ^ 2 = 1) (heven : χ.Even) : (characterGaussSum χ).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (characterGaussSum χ) = characterGaussSum χ
  rw [characterGaussSum_conj χ hreal, heven, one_mul]

theorem even_characterGaussSum_abs_re (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    |(characterGaussSum χ).re| = Real.sqrt (r : ℝ) := by
  rw [Complex.abs_re_eq_norm.mpr (even_characterGaussSum_im χ hreal heven)]
  exact hprimitive.norm_gaussSum_stdAddChar hr

theorem even_characterGaussSum_re_sq (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    (characterGaussSum χ).re ^ 2 = (r : ℝ) := by
  have h := congrArg (fun x : ℝ ↦ x ^ 2)
    (even_characterGaussSum_abs_re χ hprimitive hreal heven hr)
  simpa only [sq_abs, Real.sq_sqrt (Nat.cast_nonneg r)] using h

theorem evenCharacter_LFunction_one_signed (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    (characterGaussSum χ).re * (χ.LFunction 1).re =
      -(∑ a : ZMod r, (χ a).re * Real.log ‖1 - ZMod.stdAddChar a‖) := by
  have h := congrArg Complex.re
    (realCharacter_gauss_mul_LFunction_one_log χ hprimitive hreal
      (primitiveCharacter_ne_one χ hprimitive hr))
  simpa only [Complex.mul_re, even_characterGaussSum_im χ hreal heven,
    zero_mul, sub_zero, Complex.re_sum, (character_sq_eq_one_iff_real χ).mp hreal,
    Complex.neg_re, Complex.log_re, mul_neg, sum_neg_distrib] using h

theorem evenCharacter_LFunction_one_formula (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    (χ.LFunction 1).re =
      |∑ a : ZMod r, (χ a).re * Real.log ‖1 - ZMod.stdAddChar a‖| /
        Real.sqrt (r : ℝ) := by
  have hp := DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one hreal
    (primitiveCharacter_ne_one χ hprimitive hr)
  have h := congrArg abs (evenCharacter_LFunction_one_signed χ hprimitive hreal heven hr)
  rw [abs_mul, even_characterGaussSum_abs_re χ hprimitive hreal heven hr,
    abs_of_pos hp, abs_neg] at h
  exact (eq_div_iff (Real.sqrt_ne_zero'.mpr (by exact_mod_cast NeZero.pos r))).mpr
    (by simpa only [mul_comm] using h)

theorem evenCharacter_product_eq_real_exp (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    characterCyclotomicProduct χ =
      (Real.exp (-(characterGaussSum χ).re * (χ.LFunction 1).re) : ℂ) := by
  have him := DirichletCharacter.LFunction_apply_one_im_eq_zero_of_sq_eq_one hreal
    (primitiveCharacter_ne_one χ hprimitive hr)
  rw [characterCyclotomicProduct_eq_exp_LFunction χ hprimitive hreal
    (primitiveCharacter_ne_one χ hprimitive hr), Complex.ofReal_exp]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, even_characterGaussSum_im χ hreal heven, him]

theorem evenCharacter_product_pos (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    0 < (characterCyclotomicProduct χ).re := by
  rw [evenCharacter_product_eq_real_exp χ hprimitive hreal heven hr, Complex.ofReal_re]
  exact Real.exp_pos _

theorem evenCharacter_product_im (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    (characterCyclotomicProduct χ).im = 0 := by
  rw [evenCharacter_product_eq_real_exp χ hprimitive hreal heven hr, Complex.ofReal_im]

theorem evenCharacter_abs_log_product (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    |Real.log (characterCyclotomicProduct χ).re| =
      Real.sqrt (r : ℝ) * (χ.LFunction 1).re := by
  rw [evenCharacter_product_eq_real_exp χ hprimitive hreal heven hr, Complex.ofReal_re,
    Real.log_exp, abs_mul, abs_neg, even_characterGaussSum_abs_re χ hprimitive hreal heven hr,
    abs_of_pos (DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one hreal
      (primitiveCharacter_ne_one χ hprimitive hr))]

theorem evenCharacter_product_ne_one (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    characterCyclotomicProduct χ ≠ 1 := by
  intro h
  have hp := mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < r by exact_mod_cast NeZero.pos r))
    (DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one hreal
      (primitiveCharacter_ne_one χ hprimitive hr))
  rw [← evenCharacter_abs_log_product χ hprimitive hreal heven hr, h] at hp
  simp at hp

end LiuWang.Proof.EffectiveLValue
