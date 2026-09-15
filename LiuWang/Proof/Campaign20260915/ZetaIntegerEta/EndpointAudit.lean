import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.SourceSumJumps
import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.MomentJumps

set_option autoImplicit false
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem actual_polynomial_one_not_continuousAt (sigma : ℝ) (n : ℕ) :
    ¬ContinuousAt (fun eta : ℝ => -(∫ y : ℝ,
      rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ 1 y)) ((n : ℝ) + 1) := by
  intro hc
  have hl := tendsto_nhds_unique (actual_polynomial_one_tendsto_left sigma n)
    (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio ((n : ℝ) + 1))))
  have hr := actual_polynomial_one_tendsto_right sigma (Nat.succ_pos n)
  simp only [Nat.cast_succ] at hr
  have hr' := tendsto_nhds_unique hr
    (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi ((n : ℝ) + 1))))
  have hg : sourceGaussianPhase ((n : ℝ) + 1) (n + 1) ≠ 0 := exp_ne_zero _
  have hp : 0 < Real.cos (Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hz : sourceGaussianPhase ((n : ℝ) + 1) (n + 1) *
      (Real.cos (Real.pi / 8) : ℂ) = 0 := by
    linear_combination -(hl.trans hr'.symm) / 2
  exact (mul_ne_zero hg (ofReal_ne_zero.mpr hp.ne')) hz

theorem actual_saddle_hankel_tendsto_left (sigma : ℝ) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun eta : ℝ =>
      rsHankelPrefactor ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
        rsHankelTiltedC1 ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
          ⌊eta⌋₊ (Real.log ((⌊eta⌋₊ : ℝ) + 1 / 2)))
      (𝓝[<] ((n : ℝ) + 1))
      (𝓝 (riemannZeta ((sigma : ℂ) + I * ((rsSaddleScale * ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) -
        sourceFiniteSums ((sigma : ℂ) + I *
          ((rsSaddleScale * ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) n)) := by
  apply expanded_hankel_tendsto_left hn (by fun_prop)
  simpa only [← ofReal_pow, add_im, ofReal_im, mul_im, I_re, I_im, zero_mul,
    one_mul, zero_add, ofReal_re] using
      sq_pos_of_pos (mul_pos rsSaddleScale_pos (show 0 < (n : ℝ) + 1 by positivity))

example {eta : ℝ} (h : 125 < eta ^ 2) :
    ∀ᶠ x : ℝ in 𝓝 eta, 125 < x ^ 2 := strict_height_eventually 125 eta h

example {eta : ℝ} (h : 2000 < eta ^ 2) :
    ∀ᶠ x : ℝ in 𝓝 eta, 2000 < x ^ 2 := strict_height_eventually 2000 eta h

#print axioms floor_eventually_left
#print axioms floor_eventually_right
#print axioms sourcePhiParameter_tendsto_left
#print axioms sourcePhiParameter_tendsto_right
#print axioms rsPhi_endpoint_one
#print axioms rsPhi_endpoint_neg_one
#print axioms phi_deriv_tendsto_left
#print axioms phi_deriv_tendsto_right
#print axioms phi_tendsto_left
#print axioms phi_tendsto_right
#print axioms phiOne_tendsto_left
#print axioms phiOne_tendsto_right
#print axioms phiTwo_tendsto_left
#print axioms phiTwo_tendsto_right
#print axioms correctionMoment_continuous
#print axioms correctionMoment_tendsto_left
#print axioms correctionMoment_tendsto_right
#print axioms signed_phi_correction_jump
#print axioms saddleCoefficient_continuousAt
#print axioms sourcePolynomialExpression_continuousAt
#print axioms actual_polynomial_tendsto_left
#print axioms actual_polynomial_tendsto_right
#print axioms sourceGaussianPhase_endpoint_jump
#print axioms actual_polynomial_one_tendsto_left
#print axioms actual_polynomial_one_tendsto_right
#print axioms strict_height_eventually
#print axioms gaussianJet_parity_factor
#print axioms correctionMoment_parity
#print axioms correctionMoment_endpoint_parity
#print axioms sourcePolynomial_endpoint_jump
#print axioms sourcePolynomial_seven_endpoint_jump
#print axioms sourceFiniteSums_succ
#print axioms sourceFiniteSums_continuousAt
#print axioms sourceFiniteSums_tendsto_left
#print axioms sourceFiniteSums_tendsto_right
#print axioms expanded_hankel_remainder
#print axioms expanded_hankel_index_jump
#print axioms expanded_hankel_tendsto_left
#print axioms expanded_hankel_tendsto_right
#print axioms actual_polynomial_one_not_continuousAt
#print axioms actual_saddle_hankel_tendsto_left

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
