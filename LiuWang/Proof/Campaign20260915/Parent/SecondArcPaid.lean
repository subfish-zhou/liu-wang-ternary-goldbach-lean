import LiuWang.Proof.Campaign20260915.SecondTerminal.Audit
import LiuWang.Proof.Campaign20260915.MajorArc.RootAssembly

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.Campaign20260915.Parent.SecondArcPaid

theorem threeOddPrimes_of_major_third_and_shared_inputs {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hmajor : 0.5437 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hseven : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) 
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) * ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N :=
  MajorArc.threeOddPrimes_of_original_arcs hN hmajor
    (SecondTerminal.M2_integral_original_4012 hN hRS hseven hnu) hthird

#print axioms threeOddPrimes_of_major_third_and_shared_inputs
end LiuWang.Proof.Campaign20260915.Parent.SecondArcPaid

#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.M2_integral_original_4012
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.M2_original_4012
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.S_le_original_low_high
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.S_le_original_low_remaining
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.S_le_original_low_remaining_region_paid
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.S_le_original_outer_packets
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.S_original_4012
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.actual_last_strip_inner_T2
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.actual_last_strip_le_fixed_scalar
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.actual_last_strip_log_bound_T2
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.actual_last_strip_original_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.actual_last_strip_partition_bound
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.actual_two_strips_log_bound_T2
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.affine_last_integrand_le
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.alphaMass_add
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpointFirstBill_normalization
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpointFirstScalar_fixed
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpointFirstScalar_le_base
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpointFirstScalar_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpointSecondScalar_fixed
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpointSecondScalar_le_base
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpointSecondScalar_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_14000_original_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_16541_original_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_correction_product_le
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_density_first_remaining
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_exponential_le
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_first_base_phase
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_first_original_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_first_original_payment_of_totient
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_first_rpow_normalization
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_large_prime_ratio
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_prime_ratio_power
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_second_base_phase
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_sqrt_normalization
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_totient_bound
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_totient_fixed_certificate
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.endpoint_totient_power_bound
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.exp_difference_integral
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.exp_endpoint_first_base
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.exp_endpoint_second_base
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.exp_neg_five_le
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.heightMass_add
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.highPacket_eq_original_middle_add_high
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.inducing_source_of_real_low_zero
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastFixedCellValue_le_upper
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastFixedKernel_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastFixedKernel_integral_le_cell
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastFixedKernel_nonneg
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastFixedPoint_ge
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastFixedPoint_monotone
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastKernel_as_integral
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastKernel_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastKernel_fixed_le
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastKernel_le_signed_cell
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastKernel_nonneg
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastKernel_phase_form
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.lastKernel_scaled
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_0
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_1
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_10
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_11
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_12
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_13
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_14
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_15
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_16
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_17
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_18
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_19
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_2
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_20
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_21
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_22
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_23
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_24
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_25
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_26
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_27
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_28
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_29
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_3
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_30
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_31
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_4
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_5
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_6
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_7
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_8
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_cell_9
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_fixed_rational_budget
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_fixed_tangent_domain
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_integral_le_cell
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.last_integral_le_partition
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.low_cap_of_no_inducing_source
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.one_le_endpointPrimeCorrection
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.originalLastScalar_fixed
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.originalLastScalar_fixed_enclosure
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.originalLastScalar_fixed_partition
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.originalLastScalar_fixed_rational_reduction
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.originalLastScalar_le_base
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.originalLastScalar_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_c1_packet_coefficients
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_c1_packet_endpoint_paid_of_totient
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_c1_packet_paid
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_c1_packet_region_paid
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_c1_packet_remaining
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_exceptional_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_height_split
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_high_T1_input
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_high_packet_le_highSum
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_high_packet_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_high_packet_region_paid
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_low_packet_absence
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_low_packet_cases
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_low_packet_inducing
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_low_packet_le_closed_mass
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_nu_sqrt_bound
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_nu_sqrt_scaling
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_outer_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_outer_scalar
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_packet_density_remaining
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_packet_reduction
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_sqrt_cube
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_sqrt_totient_le
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.original_truncated_height_split
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.perron_original_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.principal_original_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.shifted_phase_gain_forty
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.source_57_original_coefficients
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.theorem_two_closed_count
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.theorem_two_input
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.truncated_endpoint_density_remaining
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.truncated_endpoint_first_remaining
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.truncated_endpoint_original_payment
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.truncated_endpoint_original_payment_of_totient
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.upperLog_base_lower
#print axioms LiuWang.Proof.Campaign20260915.SecondTerminal.zeroPacket_eq_original_three_packets
