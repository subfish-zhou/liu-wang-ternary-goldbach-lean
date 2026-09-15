import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.SourceJumpCompensation

/-! Actual C2 zeta formula at positive integer parameters via right limits.
No value is assigned to an unproved pole-crossing integral at the integer itself.
The uniform safety margin for strict original remainder bounds remains separate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology
namespace LiuWang.Proof.Campaign20260915.Parent.IntegerEtaAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaIntegerEta

theorem actual_integer_C2_right_limit (sigma : ℝ) (hs : sigma ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun eta : ℝ =>
      let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
      sourceFiniteSums s ⌊eta⌋₊ + rsHankelPrefactor s * rsSourceC2 s eta ⌊eta⌋₊)
      (𝓝[>] (n : ℝ))
      (𝓝 (riemannZeta ((sigma : ℂ) + I * ((rsSaddleScale * (n : ℝ) : ℝ) : ℂ) ^ 2))) :=
  actual_C2_zeta_formula_tendsto_right sigma hs hn

#print axioms actual_integer_C2_right_limit
end LiuWang.Proof.Campaign20260915.Parent.IntegerEtaAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.floor_eventually_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.floor_eventually_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourcePhiParameter_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourcePhiParameter_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.rsPhi_endpoint_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.rsPhi_endpoint_neg_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phi_deriv_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phi_deriv_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phi_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phi_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phiOne_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phiOne_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phiTwo_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.phiTwo_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.correctionMoment_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.correctionMoment_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.correctionMoment_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.signed_phi_correction_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.saddleCoefficient_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourcePolynomialExpression_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_polynomial_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_polynomial_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceGaussianPhase_endpoint_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_polynomial_one_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_polynomial_one_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.strict_height_eventually
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceFiniteSums_succ
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceFiniteSums_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceFiniteSums_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceFiniteSums_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.expanded_hankel_remainder
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.expanded_hankel_index_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.expanded_hankel_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.expanded_hankel_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.gaussianJet_parity_factor
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.correctionMoment_parity
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.correctionMoment_endpoint_parity
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourcePolynomial_endpoint_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourcePolynomial_seven_endpoint_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_polynomial_one_not_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_saddle_hankel_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceZetaPolynomialRemainder_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceZetaPolynomialRemainder_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceZetaPolynomialRemainder_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceZetaPolynomialRemainder_norm_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceZetaPolynomialRemainder_eq_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceZetaPolynomialRemainder_eq_C2
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_C2_polynomial_remainder_tendsto_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_C2_polynomial_remainder_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.localPrefactor_integer_independent
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.sourceZetaPolynomialRemainder_endpoint_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaIntegerEta.actual_C2_zeta_formula_tendsto_right
