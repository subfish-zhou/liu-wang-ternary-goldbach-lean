import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowAssembly

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment

example : (71 / 2 : ℝ) ≤ (63 / 128) * 36 + 0.2067 * 3100 / 36 := by
  have h := coupled_amgm (L := 3100) le_rfl (s := 36) (by norm_num)
  simpa only [show (3100 : ℝ) / 3100 = 1 by norm_num, Real.sqrt_one, mul_one] using h

example (q : ℕ) [NeZero q] : lowStripBill 1 q = 0 := by
  simp [lowStripBill, betaKernel]

example (q : ℕ) [NeZero q] :
    lowBetaBill 1 q =
      (Real.sqrt q / q.totient) * (lowCoefficient (1 / 2) * familyCount q (1 / 2) lowHeight) := by
  simp [lowBetaBill, betaKernel]

#check equation_5_25
#check equation_5_23
#check sigma4_two_source_pieces_paid

#print axioms lowHeight_log_le_eleven
#print axioms totient_constant_le_six
#print axioms totient_coupled_decay
#print axioms coupled_amgm
#print axioms sqrt_exponential_decay
#print axioms low_strip_coupled_decay
#print axioms strip_endpoint_certificate
#print axioms lowStripBill
#print axioms lowCoefficient_le_inverse
#print axioms low_strip_table_envelope
#print axioms equation_5_25_stronger
#print axioms equation_5_25
#print axioms log_5001_le
#print axioms lowHeight_shift_log_le
#print axioms low_gamma_bound
#print axioms low_uniform_horizontal
#print axioms low_uniform_nonprincipal
#print axioms low_uniform_principal
#print axioms low_count_character
#print axioms low_count_family
#print axioms low_count_family_source
#print axioms lowCoefficient_half_le
#print axioms fifth_power_decay
#print axioms low_beta_endpoint_certificate
#print axioms low_beta_global_decay
#print axioms low_beta_scalar_paid
#print axioms lowBetaBill
#print axioms low_beta_integral_count_bound
#print axioms low_beta_count_envelope
#print axioms equation_5_23_stronger
#print axioms equation_5_23
#print axioms low_character_integrable
#print axioms low_family_partialSummation
#print axioms sigma4_eq_low_family
#print axioms sigma4_full_count_partialSummation
#print axioms remainingLowBill
#print axioms low_bill_decomposition
#print axioms sigma4_two_source_pieces_paid

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment
