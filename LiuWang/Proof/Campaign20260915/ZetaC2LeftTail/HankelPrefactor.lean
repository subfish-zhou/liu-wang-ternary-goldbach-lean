import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.IntegralBudget
import LiuWang.Proof.Campaign20260915.ZetaC2RightTail.Prefactor

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem critical_gamma_norm_sq {s : ℂ} (hs : s.re = 1 / 2) :
    ‖Gamma s‖ ^ 2 = Real.pi / Real.cosh (Real.pi * s.im) := by
  have he : s = (1 / 2 : ℂ) + I * s.im := by
    apply Complex.ext <;> simp [hs]
  simpa only [← he] using
    LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_gamma_norm_sq s.im

theorem critical_hankel_jump_norm {s : ℂ} (hs : s.re = 1 / 2) :
    ‖exp (2 * Real.pi * I * s) - 1‖ = 1 + Real.exp (-2 * Real.pi * s.im) := by
  have he : s = (1 / 2 : ℂ) + I * s.im := by
    apply Complex.ext <;> simp [hs]
  simpa only [← he] using
    LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_jump_norm s.im

theorem critical_hankel_numerator_norm_sq {s : ℂ} (hs : s.re = 1 / 2) :
    ‖exp (log (2 * Real.pi : ℂ) * s + Real.pi * I * s / 2)‖ ^ 2 =
      2 * Real.pi * Real.exp (-Real.pi * s.im) := by
  have hl : log (2 * Real.pi : ℂ) = (Real.log (2 * Real.pi) : ℂ) := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    exact (ofReal_log (by positivity)).symm
  rw [hl, norm_exp, pow_two, ← Real.exp_add]
  have he : ((Real.log (2 * Real.pi) : ℂ) * s + Real.pi * I * s / 2).re +
      ((Real.log (2 * Real.pi) : ℂ) * s + Real.pi * I * s / 2).re =
      Real.log (2 * Real.pi) + (-Real.pi * s.im) := by
    simp [hs]
    ring
  rw [he, Real.exp_add, Real.exp_log (by positivity)]

theorem critical_hankel_prefactor_norm_sq {s : ℂ} (hs : s.re = 1 / 2) :
    ‖rsHankelPrefactor s‖ ^ 2 = 1 / (1 + Real.exp (-2 * Real.pi * s.im)) := by
  have he : s = (1 / 2 : ℂ) + I * s.im := by
    apply Complex.ext <;> simp [hs]
  simpa only [← he] using
    LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactor_norm_sq s.im

theorem critical_hankel_prefactor_norm_le_one {s : ℂ} (hs : s.re = 1 / 2) :
    ‖rsHankelPrefactor s‖ ≤ 1 := by
  have hsq := critical_hankel_prefactor_norm_sq hs
  have h : 1 / (1 + Real.exp (-2 * Real.pi * s.im)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.exp_pos (-2 * Real.pi * s.im)]
  nlinarith [norm_nonneg (rsHankelPrefactor s)]

end LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
