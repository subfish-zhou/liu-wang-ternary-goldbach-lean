import LiuWang.Proof.Campaign20260915.ZetaC2RightTail.SourceError

/-! Actual full right C2 tail with the original Hankel prefactor.
The left branch, central Jn and complete zeta remainder remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Set MeasureTheory
open scoped Real
namespace LiuWang.Proof.Campaign20260915.Parent.RightC2TailAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaC2RightTail

theorem actual_prefactored_right_tail {eta : ℝ} (he : 1 ≤ eta) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
      (∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand
        ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta ⌊eta⌋₊ y)‖ ≤
      11 / (2 * Real.pi) * eta ^ (-(3 / 2 : ℝ)) *
        Real.exp (-((rsSaddleScale * eta) ^ 2) / 11) :=
  critical_prefactored_right_tail_effective he (Nat.lt_floor_add_one eta).le

#print axioms actual_prefactored_right_tail
end LiuWang.Proof.Campaign20260915.Parent.RightC2TailAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.rightTailDenom_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.rightTailRate_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_coordinates
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_log_im
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_phase_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_denominator_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_integrand_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_integrand_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_majorant_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_tail_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_tail_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.right_tail_bound_floor
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.sourceC2_truncation_right_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_gamma_norm_sq
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_jump_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactor_norm_sq
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactor_norm_le_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactored_right_tail
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.rightTailDenom_half
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.rightTailBudget_effective
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_prefactored_right_tail_effective
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_sourceC2_truncation_right_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2RightTail.critical_sourceC2_floor_right_error
