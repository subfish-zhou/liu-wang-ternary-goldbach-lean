import LiuWang.Proof.EffectiveLValue.OddHelpers.IntegerSum
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticValueAtOnePositive

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Complex Finset

theorem arg_one_sub_exp_two_pi {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    Complex.arg (1 - Complex.exp (2 * Real.pi * x * Complex.I)) =
      Real.pi * x - Real.pi / 2 := by
  have hsin : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx) (by nlinarith [Real.pi_pos])
  have he : (1 - Complex.exp (2 * Real.pi * x * Complex.I)) =
      (2 * Real.sin (Real.pi * x) : ℝ) *
        (Real.cos (Real.pi * x - Real.pi / 2) +
          Real.sin (Real.pi * x - Real.pi / 2) * Complex.I) := by
    rw [show (2 : ℂ) * Real.pi * x * I = ((2 * (Real.pi * x) : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.sub_im, Complex.one_im, Complex.add_im, Complex.mul_im,
        mul_zero, mul_one, zero_mul, add_zero, zero_add, sub_zero,
        Real.cos_two_mul, Real.sin_two_mul, Real.cos_sub_pi_div_two,
        Real.sin_sub_pi_div_two]
    · nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
    · ring
  rw [he]
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  apply Complex.arg_mul_cos_add_sin_mul_I (by positivity)
  constructor <;> nlinarith [Real.pi_pos]

variable {r : ℕ} [NeZero r]

theorem stdAddChar_log_im (a : ZMod r) (ha : a ≠ 0) :
    (Complex.log (1 - ZMod.stdAddChar a)).im =
      Real.pi * (a.val : ℝ) / r - Real.pi / 2 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have ha0 : (0 : ℝ) < a.val := by
    exact_mod_cast (Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha))
  have har : (a.val : ℝ) < r := by exact_mod_cast a.val_lt
  have he : ZMod.stdAddChar a =
      Complex.exp (2 * Real.pi * ((a.val : ℝ) / r) * Complex.I) := by
    have h := ZMod.stdAddChar_coe (N := r) (a.val : ℤ)
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at h
    rw [h]
    congr 1
    push_cast
    ring
  rw [Complex.log_im, he]
  convert arg_one_sub_exp_two_pi (div_pos ha0 hr) ((div_lt_one hr).mpr har) using 1 <;>
    push_cast <;> ring

theorem oddCharacter_LFunction_one_signed (χ : OddRealPrimitiveCharacter r) :
    (characterGaussSum χ.1).im * (χ.1.LFunction 1).re =
      -(Real.pi / r) * (oddCharacterMoment χ : ℝ) := by
  have him := DirichletCharacter.LFunction_apply_one_im_eq_zero_of_sq_eq_one
    χ.2.2.1 (oddCharacter_ne_one χ)
  have h := congrArg Complex.im (oddCharacter_gauss_mul_LFunction_one_log χ)
  simp only [Complex.mul_im, him, mul_zero, zero_add, Complex.im_sum] at h
  rw [h]
  have hsum : ∑ a : ZMod r, (χ.1 a).re = 0 := by
    simpa only [← Complex.re_sum, Complex.zero_re] using
      congrArg Complex.re (χ.1.sum_eq_zero_of_ne_one (oddCharacter_ne_one χ))
  calc
    _ = ∑ a : ZMod r, (χ.1 a).re *
        (-(Real.pi * (a.val : ℝ) / r - Real.pi / 2)) := by
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · subst a
        simp [oddCharacter_zero]
      · rw [(character_sq_eq_one_iff_real χ.1).mp χ.2.2.1,
          zero_mul, add_zero, Complex.neg_im, stdAddChar_log_im a ha]
    _ = -(Real.pi / r) * (∑ a : ZMod r, (χ.1 a).re * a.val) +
        (Real.pi / 2) * (∑ a : ZMod r, (χ.1 a).re) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [hsum, mul_zero, add_zero]
      simp [oddCharacterMoment, oddCharacterInt_re]

theorem oddCharacter_LFunction_one_formula (χ : OddRealPrimitiveCharacter r)
    (hr : 1 < r) :
    (χ.1.LFunction 1).re =
      (Real.pi / Real.sqrt (r : ℝ)) * (|(oddCharacterMoment χ : ℝ)| / r) := by
  have hpos := DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one
    χ.2.2.1 (oddCharacter_ne_one χ)
  have hre : (characterGaussSum χ.1).re = 0 := by
    have h := characterGaussSum_conj χ.1 χ.2.2.1
    rw [χ.2.2.2, neg_one_mul] at h
    have hh := congrArg Complex.re h
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hh
    linarith
  have hnorm : |(characterGaussSum χ.1).im| = Real.sqrt (r : ℝ) := by
    rw [Complex.abs_im_eq_norm.mpr hre]
    exact χ.2.1.norm_gaussSum_stdAddChar hr
  have h := congrArg abs (oddCharacter_LFunction_one_signed χ)
  rw [abs_mul, hnorm, abs_of_pos hpos, abs_mul, abs_neg,
    abs_of_pos (div_pos Real.pi_pos (by exact_mod_cast NeZero.pos r))] at h
  have hs : Real.sqrt (r : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast NeZero.pos r)
  apply (mul_right_inj' hs).mp
  calc
    Real.sqrt (r : ℝ) * (χ.1.LFunction 1).re =
        Real.pi / r * |(oddCharacterMoment χ : ℝ)| := h
    _ = _ := by field_simp

theorem oddCharacterMoment_ne_zero (χ : OddRealPrimitiveCharacter r) (hr : 1 < r) :
    oddCharacterMoment χ ≠ 0 := by
  intro h
  have hp := DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one
    χ.2.2.1 (oddCharacter_ne_one χ)
  rw [oddCharacter_LFunction_one_formula χ hr, h] at hp
  simp at hp

end LiuWang.Proof.EffectiveLValue
