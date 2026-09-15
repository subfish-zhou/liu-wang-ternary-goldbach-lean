import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.SpectralConsumer

/-! The original (3.38) is unconditional for all positive real x.
The finite-theta input in (4.12) is separate and remains unpaid.
Local elementary estimates use the existing log(4) bound and certified small theta data.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LiuWang.Proof.Campaign20260915.Parent.PrimePowerAudit
open LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

theorem actual_equation_3_38 {x : ℝ} (hx : 0 < x) :
    Chebyshev.psi x - Chebyshev.theta x <
      Chebyshev.theta (Real.sqrt x) + 3 * x ^ (1 / (3 : ℝ)) :=
  equation_3_38 hx

#print axioms actual_equation_3_38
end LiuWang.Proof.Campaign20260915.Parent.PrimePowerAudit

#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.psi_sub_theta_eq_sqrt_add_sum
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_eq_sum
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.sqrt_theta_le_psi_sub_theta
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_mono
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_le_elementary_sum
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_le_local_sum
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.log_cutoff_of_lt_pow_two
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_lower_of_psi_lower
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_lower_of_psi_lower_elementary
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.root_ratio_bound
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.middleCoefficient_certificate
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.middleCoefficient_sum
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.middle_sum_lt_three
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.elementary_sum_lt_three
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_upper_pilot
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higher_upper_pilot
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_le_upper_units
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.floor_root_eq_nthRoot
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_root_eq_nthRoot
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_nat_le_upper_units
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_upper_certificate
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higher_upper_certificate
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_lt_self_up_to_256
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_le_self_up_to_256
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_lt_three_small
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.higherPrimePowers_lt_three
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.equation_3_38
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.psi_sub_theta_lt_elementary
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.equation_4_12_of_finite_theta
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_bounds_of_psi_bounds_raw
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.theta_bounds_of_psi_bounds_finite
#print axioms LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.rsTheta_original_moment_bounds_raw
