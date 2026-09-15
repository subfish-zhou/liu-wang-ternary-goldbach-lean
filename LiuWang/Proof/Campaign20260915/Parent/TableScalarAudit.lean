import LiuWang.Proof.Campaign20260915.RSTableCertificates.Coverage

/-! Certified scalar rows and continuous coverage, not actual Table I zero moments.
The spectrum-to-budget hypotheses remain explicit in the psi consumers.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LiuWang.Proof.Campaign20260915.Parent.TableScalarAudit
open LiuWang.Proof.Campaign20260915.RSTableCertificates

theorem actual_lower_scalar_cover {x : ℝ} (hx : Real.exp (18.4 : ℝ) ≤ x)
    (hx' : x ≤ Real.exp (375 : ℝ)) :
    ∃ s ∈ lowerSegments, s.1.Valid ∧ Real.exp (s.1.b : ℝ) ≤ x ∧
      (s.1.e : ℝ) ≤ 0.307 / Real.log x :=
  lower_cover hx hx'

theorem actual_upper_scalar_cover {x : ℝ} (hx : Real.exp (375 : ℝ) ≤ x)
    (hx' : x ≤ Real.exp (5000 : ℝ)) :
    ∃ s ∈ upperSegments, s.1.Valid ∧ Real.exp (s.1.b : ℝ) ≤ x ∧
      (s.1.e : ℝ) ≤ 0.47 / Real.log x :=
  upper_cover hx hx'

#print axioms actual_lower_scalar_cover
#print axioms actual_upper_scalar_cover
end LiuWang.Proof.Campaign20260915.Parent.TableScalarAudit

#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.exp_certificate_sound
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.coefficient_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.epsilon_cast
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row_exp_bounds
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row_budget
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row_cut
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row_epsilon_gap
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row_root
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.trivial_kernel_le_one
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.absorb_remainders
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row_psi_of_actual_moment
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.constant_error_on_log_interval
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row375_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row4900_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row5000_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row18_4_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row18_5_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row18_7_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row18_8_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row19_5_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row21_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row28_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row72_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row225_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row325_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row350_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row575_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row675_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row750_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row800_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row825_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row850_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row875_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row900_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row925_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row950_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row975_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row1000_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row1050_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row1100_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row1150_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row1200_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row1300_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row1500_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row2000_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row4500_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.lower_chain
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.upper_chain
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.lower_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.upper_valid
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.endpoint_nonmonotone
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.chain_sound
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.certified_cover
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.lower_cover
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.upper_cover
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.budget_eq_original
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.row_original_root
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.cover_psi_of_moments
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.lower_psi_of_moments
#print axioms LiuWang.Proof.Campaign20260915.RSTableCertificates.upper_psi_of_moments
