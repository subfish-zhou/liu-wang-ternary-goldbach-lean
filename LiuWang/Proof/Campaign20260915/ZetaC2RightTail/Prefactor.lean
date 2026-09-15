import LiuWang.Proof.Campaign20260915.ZetaC2RightTail.TailIntegral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Real ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaC2RightTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem critical_gamma_norm_sq (t : ℝ) :
    ‖Gamma ((1 / 2 : ℂ) + I * t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hc : 1 - ((1 / 2 : ℂ) + I * t) = conj ((1 / 2 : ℂ) + I * t) := by
    apply Complex.ext <;> simp
    ring
  have hs : sin (Real.pi * ((1 / 2 : ℂ) + I * t)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + I * t) =
      (Real.pi : ℂ) / 2 + (Real.pi * t : ℝ) * I by push_cast; ring]
    rw [sin_add_mul_I, sin_pi_div_two, cos_pi_div_two]
    simp
  have h := congrArg norm (Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + I * t))
  rw [hc, Gamma_conj, norm_mul, norm_conj, hs, norm_div,
    norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)] at h
  nlinarith

theorem critical_jump_norm (t : ℝ) :
    ‖exp (2 * Real.pi * I * ((1 / 2 : ℂ) + I * t)) - 1‖ =
      1 + Real.exp (-2 * Real.pi * t) := by
  have he : exp (2 * Real.pi * I * ((1 / 2 : ℂ) + I * t)) =
      -(Real.exp (-2 * Real.pi * t) : ℂ) := by
    rw [show 2 * Real.pi * I * ((1 / 2 : ℂ) + I * t) =
      (-2 * Real.pi * t : ℝ) + (Real.pi : ℂ) * I by
        push_cast
        ring_nf
        rw [I_sq]
        ring, exp_add, exp_pi_mul_I, mul_neg_one, ofReal_exp]
  rw [he, show -(Real.exp (-2 * Real.pi * t) : ℂ) - 1 =
    -((1 + Real.exp (-2 * Real.pi * t) : ℝ) : ℂ) by push_cast; ring,
    norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem critical_prefactor_norm_sq (t : ℝ) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * t)‖ ^ 2 =
      1 / (1 + Real.exp (-2 * Real.pi * t)) := by
  have hn :
      ‖exp (log (2 * Real.pi : ℂ) * ((1 / 2 : ℂ) + I * t) +
        Real.pi * I * ((1 / 2 : ℂ) + I * t) / 2)‖ ^ 2 =
        2 * Real.pi * Real.exp (-Real.pi * t) := by
    rw [norm_exp, pow_two, ← Real.exp_add]
    have hl : log (2 * Real.pi : ℂ) = (Real.log (2 * Real.pi) : ℂ) := by
      simpa only [ofReal_mul, ofReal_ofNat] using
        (ofReal_log (show (0 : ℝ) ≤ 2 * Real.pi by positivity)).symm
    rw [hl]
    simp [mul_re, mul_im]
    rw [show (Real.log (2 * Real.pi) * 2⁻¹ + - (Real.pi * t) / 2) +
      (Real.log (2 * Real.pi) * 2⁻¹ + - (Real.pi * t) / 2) =
        Real.log (2 * Real.pi) + (-(Real.pi * t)) by ring,
      Real.exp_add, Real.exp_log (by positivity)]
  have he1 : Real.exp (Real.pi * t) * Real.exp (-Real.pi * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have he2 : Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) =
      Real.exp (-2 * Real.pi * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [rsHankelPrefactor, norm_div, norm_mul, norm_inv, div_pow, mul_pow,
    hn, inv_pow, critical_gamma_norm_sq, critical_jump_norm]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hc : Real.cosh (Real.pi * t) ≠ 0 := (Real.cosh_pos _).ne'
  have hd : 1 + Real.exp (-2 * Real.pi * t) ≠ 0 := by positivity
  field_simp
  rw [Real.cosh_eq]
  simp only [neg_mul] at he1 he2
  nlinarith

theorem critical_prefactor_norm_le_one (t : ℝ) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * t)‖ ≤ 1 := by
  have h := critical_prefactor_norm_sq t
  have hd : 0 < 1 + Real.exp (-2 * Real.pi * t) := by positivity
  have hh : 1 / (1 + Real.exp (-2 * Real.pi * t)) ≤ 1 := by
    rw [div_le_iff₀ hd]
    linarith [Real.exp_pos (-2 * Real.pi * t)]
  nlinarith [norm_nonneg (rsHankelPrefactor ((1 / 2 : ℂ) + I * t))]

theorem critical_prefactored_right_tail {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm : eta ≤ (m : ℝ) + 1) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
      (∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand
        ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m y)‖ ≤
      rightTailBudget (1 / 2) eta := by
  rw [norm_mul]
  have hp := critical_prefactor_norm_le_one ((rsSaddleScale * eta) ^ 2)
  rw [ofReal_pow] at hp
  have hb := right_tail_bound (sigma := 1 / 2) (by norm_num) he hm
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hb
  exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans hb

end LiuWang.Proof.Campaign20260915.ZetaC2RightTail
