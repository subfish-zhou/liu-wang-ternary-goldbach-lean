import LiuWang.Proof.Campaign20260915.RSMertensTransport.RealTransport
import LiuWang.Proof.Campaign20260915.Parent.WeightedPsiAudit
import LiuWang.Proof.Campaign20260915.RSSection8Scalar.PrimePowerIntegral
import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.Main

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set AnalyticNumberTheory.Mertens
open LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
open LiuWang.Proof.Campaign20260915.RSSection8Scalar
open LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections
open LiuWang.Proof.Campaign20260915.Parent.WeightedPsiAudit

namespace LiuWang.Proof.Campaign20260915.RSMertensTransport

def primePowerErrorKernel (t : ℝ) : ℝ :=
  (Chebyshev.psi t - Chebyshev.theta t) * (1 + Real.log t) /
    (t ^ 2 * Real.log t ^ 2)

theorem thetaErrorKernel_split (t : ℝ) :
    thetaErrorKernel t = -signedPsiError t - primePowerErrorKernel t := by
  unfold thetaErrorKernel signedPsiError weight primePowerErrorKernel
  ring

theorem primePowerErrorKernel_nonneg {t : ℝ} (ht : 1 < t) :
    0 ≤ primePowerErrorKernel t := by
  have h := Chebyshev.theta_le_psi t
  have hl := Real.log_pos ht
  unfold primePowerErrorKernel
  positivity

theorem primePowerErrorKernel_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn primePowerErrorKernel (Ioi x) := by
  have htheta := integrableOn_thetaErrorKernel.mono_set (Ioi_subset_Ioi hx)
  have hpsi := signedPsiError_integrableOn (by linarith : 1 < x)
  apply (htheta.neg.sub hpsi).congr
  exact Filter.Eventually.of_forall fun t => by
    have h := thetaErrorKernel_split t
    dsimp
    linarith

theorem reciprocal_error_eq_signed_psi {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ - (Real.log (Real.log x) + mertensSecondConstant) =
      (Chebyshev.theta x - x) / (x * Real.log x) +
        (∫ t in Ioi x, signedPsiError t) +
        ∫ t in Ioi x, primePowerErrorKernel t := by
  rw [mertensSecond_error_decomposition hx]
  have hfun : thetaErrorKernel = fun t => -signedPsiError t - primePowerErrorKernel t :=
    funext thetaErrorKernel_split
  rw [hfun, integral_sub (signedPsiError_integrableOn (by linarith)).neg
    (primePowerErrorKernel_integrable hx), integral_neg]
  ring

theorem primePowerErrorKernel_integral_le {x : ℝ} (hx : 2 ≤ x)
    (hsqrt : ∀ t ∈ Ioi x, Chebyshev.theta (Real.sqrt t) ≤ 1.02 * Real.sqrt t) :
    (∫ t in Ioi x, primePowerErrorKernel t) ≤
      (2.04 / x ^ (1 / 2 : ℝ) + 4.5 * x ^ (-2 / 3 : ℝ)) / Real.log x := by
  apply (setIntegral_mono_on (primePowerErrorKernel_integrable hx)
    (primePowerIntegrand_integrable (by linarith)) measurableSet_Ioi ?_).trans
    (primePower_integral_le (by linarith))
  intro t ht
  have ht0 : 0 < t := by linarith [show x < t from ht]
  have hpp := equation_3_38 ht0
  have hs := hsqrt t ht
  have hbound : Chebyshev.psi t - Chebyshev.theta t ≤
      1.02 * t ^ (1 / 2 : ℝ) + 3 * t ^ (1 / 3 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    linarith
  have hl := Real.log_pos (by linarith [show x < t from ht] : 1 < t)
  unfold primePowerErrorKernel primePowerIntegrand
  gcongr

theorem reciprocal_error_scaled_lt_L {x : ℝ} (hx : 2 ≤ x)
    (hsqrt : ∀ t ∈ Ioi x, Chebyshev.theta (Real.sqrt t) ≤ 1.02 * Real.sqrt t) :
    Real.log x *
        |primeReciprocalSum ⌊x⌋₊ - (Real.log (Real.log x) + mertensSecondConstant)| <
      |Chebyshev.theta x - x| / x + L x - 1.02 / (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx1
  have hpp0 : 0 ≤ ∫ t in Ioi x, primePowerErrorKernel t :=
    setIntegral_nonneg measurableSet_Ioi
      (fun t ht => primePowerErrorKernel_nonneg (hx1.trans ht))
  have hpp := primePowerErrorKernel_integral_le hx hsqrt
  have hpsi := actual_psi_L_contribution hx1
  have heq : (∫ t in Ioi x,
      (t - Chebyshev.psi t) * (1 + Real.log t) / (t ^ 2 * Real.log t ^ 2)) =
      ∫ t in Ioi x, signedPsiError t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      unfold signedPsiError weight
      ring
  rw [heq, abs_mul, abs_of_pos hl] at hpsi
  have htri : |(Chebyshev.theta x - x) / (x * Real.log x) +
      (∫ t in Ioi x, signedPsiError t) +
      ∫ t in Ioi x, primePowerErrorKernel t| ≤
      |(Chebyshev.theta x - x) / (x * Real.log x)| +
        |∫ t in Ioi x, signedPsiError t| + ∫ t in Ioi x, primePowerErrorKernel t := by
    exact (abs_add_le _ _).trans (add_le_add
      (abs_add_le _ _) (le_of_eq (abs_of_nonneg hpp0)))
  have hscaled := mul_le_mul_of_nonneg_left htri hl.le
  have hppscaled := (le_div_iff₀ hl).mp hpp
  have hend : Real.log x * |(Chebyshev.theta x - x) / (x * Real.log x)| =
      |Chebyshev.theta x - x| / x := by
    rw [abs_div, abs_of_pos (mul_pos hx0 hl)]
    field_simp
  rw [reciprocal_error_eq_signed_psi hx]
  nlinarith only [hscaled, hppscaled, hpsi, hend]

theorem lemma13_from_endpoint_and_L {x a : ℝ} (hx : 2 ≤ x)
    (hsqrt : ∀ t ∈ Ioi x, Chebyshev.theta (Real.sqrt t) ≤ 1.02 * Real.sqrt t)
    (hendpoint : |Chebyshev.theta x - x| / x ≤ a / Real.log x)
    (hL : L x < M x a) :
    |primeReciprocalSum ⌊x⌋₊ - (Real.log (Real.log x) + mertensSecondConstant)| <
      Real.log (1 + 1 / (2 * Real.log x ^ 2)) -
        1.02 / ((x - 1) * Real.log x) := by
  have hl := Real.log_pos (by linarith : 1 < x)
  have hh := reciprocal_error_scaled_lt_L hx hsqrt
  have hcancel :
      (Real.log (1 + 1 / (2 * Real.log x ^ 2)) -
        1.02 / ((x - 1) * Real.log x)) * Real.log x =
      a / Real.log x + M x a - 1.02 / (x - 1) := by
    unfold M
    field_simp
    <;> ring
  apply (mul_lt_mul_iff_right₀ hl).mp
  rw [hcancel]
  nlinarith only [hh, hendpoint, hL]

#print axioms reciprocal_error_eq_signed_psi
#print axioms primePowerErrorKernel_integral_le
#print axioms reciprocal_error_scaled_lt_L
#print axioms lemma13_from_endpoint_and_L

end LiuWang.Proof.Campaign20260915.RSMertensTransport
