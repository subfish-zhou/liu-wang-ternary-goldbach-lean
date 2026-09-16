import LiuWang.Proof.Campaign20260915.RosserCount.OriginalRemainder
import LiuWang.Proof.Campaign20260915.ZetaWinding.LittlewoodPhase

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.DirichletZeroCount

def rosserGammaRemainder (T : ℝ) : ℝ :=
  (gammaLogBranch (criticalPoint T / 2)).im -
    T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8

theorem rosserGammaRemainder_normalization {T : ℝ} (hT : 0 < T) :
    Real.pi * (1 + criticalGammaArgument T / Real.pi - rosserMain T) =
      rosserGammaRemainder T := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  unfold rosserGammaRemainder rosserMain criticalGammaArgument
  simp only [Complex.sub_im, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, criticalPoint]
  rw [Real.log_div hT.ne' hp, Real.log_mul (by norm_num) Real.pi_ne_zero,
    Real.log_div hT.ne' (by norm_num)]
  field_simp
  ring

theorem positiveCount_error_decomposition {T : ℝ} (hT : 0 < T) :
    Real.pi * ((positiveCount T : ℝ) - rosserMain T) =
      Real.pi * turingS T + rosserGammaRemainder T := by
  have hg := rosserGammaRemainder_normalization hT
  unfold turingS
  nlinarith only [hg]

theorem positiveCount_error_horizontal_phase {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    Real.pi * ((positiveCount T : ℝ) - rosserMain T) =
      rosserGammaRemainder T +
        (Complex.log (riemannZeta (horizontalAt T 2)) -
          HIntegral (logDeriv riemannZeta) (1 / 2) 2 T).im := by
  rw [positiveCount_error_decomposition hT, turingS_eq_horizontal_logDeriv hT hr, add_comm]

#print axioms rosserGammaRemainder_normalization
#print axioms positiveCount_error_decomposition
#print axioms positiveCount_error_horizontal_phase

end LiuWang.Proof.Campaign20260915.RosserCount
