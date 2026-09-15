import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaPhaseTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def imagIPower (j : ℕ) : ℚ :=
  if j % 4 = 1 then 1 else if j % 4 = 3 then -1 else 0

def rationalAtanTaylor (n : ℕ) (q : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (-1) ^ (j + 1) * q ^ j * imagIPower j / j

noncomputable section

open Complex Finset

theorem log_im_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    (log z).im = Real.arctan (z.im / z.re) := by
  rw [log_im]
  have h1 := (Complex.neg_pi_div_two_lt_arg_iff).mpr (Or.inl hz)
  have h2 := (Complex.arg_lt_pi_div_two_iff).mpr (Or.inl hz)
  rw [← Complex.tan_arg, Real.arctan_tan h1 h2]

theorem imagIPower_correct (j : ℕ) : (imagIPower j : ℝ) = (I ^ j).im := by
  rw [I_pow_eq_pow_mod]
  have hj : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold imagIPower
  interval_cases h : j % 4 <;> norm_num [h, I_sq, I_pow_three]

theorem rationalAtanTaylor_correct (n : ℕ) (q : ℚ) :
    (rationalAtanTaylor n q : ℝ) = (Complex.logTaylor (n + 1) ((q : ℂ) * I)).im := by
  unfold rationalAtanTaylor Complex.logTaylor
  push_cast
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  rw [← Complex.ofReal_natCast j, ← Complex.ofReal_ratCast q,
    show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, imagIPower_correct]
  ring

theorem rationalAtanTaylor_error (n : ℕ) {q : ℚ} (hq : |q| ≤ 1 / 2) :
    |Real.arctan (q : ℝ) - (rationalAtanTaylor n q : ℝ)| ≤
      (1 / 2 : ℝ) ^ (n + 1) * 2 / (n + 1) := by
  have hqR : |(q : ℝ)| ≤ 1 / 2 := by
    have hh : ((|q| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    simpa using hh
  have hn : ‖(q : ℂ) * I‖ ≤ (1 / 2 : ℝ) := by
    simpa [norm_mul, Complex.norm_ratCast] using hqR
  have h := Complex.norm_log_sub_logTaylor_le n (lt_of_le_of_lt hn (by norm_num))
  have hi := (abs_im_le_norm (log (1 + (q : ℂ) * I) -
    Complex.logTaylor (n + 1) ((q : ℂ) * I))).trans h
  rw [sub_im, log_im_of_re_pos (by norm_num : 0 < (1 + (q : ℂ) * I).re)] at hi
  simp only [add_im, one_im, mul_im, I_im, I_re, mul_one, mul_zero, add_zero,
    zero_add, add_re, one_re, mul_re, sub_self, div_one, Complex.ratCast_re,
    Complex.ratCast_im] at hi
  rw [← rationalAtanTaylor_correct] at hi
  have hinv : (1 - ‖(q : ℂ) * I‖)⁻¹ ≤ (2 : ℝ) := by
    rw [← one_div, div_le_iff₀ (by linarith)]
    linarith
  apply hi.trans
  gcongr
  exact inv_nonneg.mpr (by linarith)

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
