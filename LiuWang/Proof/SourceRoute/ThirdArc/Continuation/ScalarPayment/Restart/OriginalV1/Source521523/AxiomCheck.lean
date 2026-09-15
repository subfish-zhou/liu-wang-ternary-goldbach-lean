import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.Assembly

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

theorem normalized_weight_literal (N : ℕ) (beta : ℝ) :
    lowCoefficient beta * (N : ℝ) ^ (beta - 1) =
      (1 - (0.001 : ℝ) ^ beta) / beta * (N : ℝ) ^ (beta - 1) := rfl

theorem single_nu_literal (L Q : ℝ) :
    (0.999 : ℝ) * L * sourceNu Q * Real.exp (-(1 / 2 : ℝ) * Real.log Q) =
      0.999 * L * (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log Q) +
        2.50637 / Real.log (Real.log Q)) * Real.exp (-(1 / 2 : ℝ) * Real.log Q) := rfl

theorem originalBaseScalar_literal (L Q : ℝ) :
    originalBaseScalar L Q =
      L * Real.sqrt Q * ((1 - (0.001 : ℝ) ^ (1 / 2 : ℝ)) / (1 / 2)) *
        (10006.8423 * Real.log Q + 76180) * Real.exp (-L / 60) := rfl

theorem lowCoefficient_half_literal :
    lowCoefficient (1 / 2) = 2 * (1 - (0.001 : ℝ) ^ (1 / 2 : ℝ)) := by
  unfold lowCoefficient
  ring

theorem originalPrimedBill_literal (N q : ℕ) [NeZero q] :
    originalPrimedBill N q =
      ((N : ℝ) * Real.sqrt q / q.totient) *
        (lowCoefficient (1 / 2) * (N : ℝ) ^ (-1 / 2 : ℝ) *
          familyCount q (1 / 2) (10000 * Real.pi) +
          ∫ alpha in (1 / 2 : ℝ)..
            (1 - 1 / (9.645908801 * Real.log ((q : ℝ) * (10000 * Real.pi)))),
            betaKernel N alpha * lowCoefficient alpha * familyCount q alpha (10000 * Real.pi)) := rfl

theorem local_c1_parameter_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    10 ≤ (q : ℝ) * lowHeight ∧ (q : ℝ) ≤ (q : ℝ) * lowHeight ∧
      (q : ℝ) * lowHeight / q = lowHeight := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  refine ⟨by linarith [(low_table_domain hN hq).1], ?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left lowHeight_ge_one hq0.le
  · field_simp

theorem local_c1_slot_unique {q : ℕ} [NeZero q]
    {e : Option ((_chi : Character q) × ℂ)} (hloc : LocalC1Data q e)
    {z w : (_chi : Character q) × ℂ}
    (hz : z ∈ rectangleZeros q (1 / 2) lowHeight)
    (hw : w ∈ rectangleZeros q (1 / 2) lowHeight)
    (hzr : Source525526.lastUpper q < z.2.re)
    (hwr : Source525526.lastUpper q < w.2.re) : z = w := by
  have hz := mem_zeroValues.mp (rectangle_mem.mp hz)
  have hw := mem_zeroValues.mp (rectangle_mem.mp hw)
  have hez := hloc.region z.1 z.2 hz.1 hz.2.1.1 hz.2.1.2.1 hz.2.1.2.2 hzr
  have hew := hloc.region w.1 w.2 hw.1 hw.2.1.1 hw.2.1.2.1 hw.2.1.2.2 hwr
  exact Option.some.inj (hez.symm.trans hew)

theorem equation_5_21_literal {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (htotient : (q : ℝ) / q.totient ≤
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log q) +
        2.50637 / Real.log (Real.log q))
    {beta : ℝ} (hb : 1 / 2 ≤ beta) (hb1 : beta < 1) :
    (Real.sqrt q / q.totient) * ((1 - (0.001 : ℝ) ^ beta) / beta) * (N : ℝ) ^ beta ≤
      (0.11585 : ℝ) * N / sourceL N :=
  equation_5_21_original hN hq htotient hb hb1

theorem equation_5_23_literal {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
      (2 * (1 - (0.001 : ℝ) ^ (1 / 2 : ℝ)) * (N : ℝ) ^ (-1 / 2 : ℝ) *
        familyCount q (1 / 2) lowHeight +
        ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      (0.00365 : ℝ) * N / sourceL N := by
  simpa only [lowBetaBill, lowCoefficient_half_literal] using equation_5_23_original hN hq1

#print originalCountFactor
#print originalBaseScalar
#print primedZeros
#print primedSigma4
#print selectedBill
#print originalPrimedBill
#print LocalC1Data
#check @LocalC1Data.mk
#check @LocalC1Data.selected_mem
#check @LocalC1Data.selected_right
#check @LocalC1Data.selected_real
#check @LocalC1Data.selected_simple
#check @LocalC1Data.selected_nonprincipal
#check @LocalC1Data.selected_real_character
#check @LocalC1Data.primitive_source
#check @LocalC1Data.region

#check @normalized_single_weight
#check @logNu_exp_sixth_antitone
#check @single_endpoint_log
#check @single_endpoint_nu
#check @single_endpoint_paid
#check @original_nu_single_scale
#check @equation_5_21_original
#check @original_base_endpoint
#check @original_base_global_decay
#check @originalBaseScalar_paid
#check @original_base_scalar_paid
#check @low_norm_ge_one
#check @source_six_low_main
#check @source_six_low_bound
#check @source_five_low_bound
#check @original_count_character
#check @original_count_family
#check @original_base_integral_cancellation
#check @original_low_beta_integral
#check @lowBetaBill_le_original_scalar
#check @equation_5_23_original
#check @rectangle_mem
#check @primed_right_boundary
#check @sigma4_exact_local_split
#check @selectedBill_paid
#check @actual_simple_lowKernel_original
#check @rectangle_upperMass
#check @primed_upperMass_le_family
#check @primedSigma4_le_original_bill
#check @original_finite_bill_decomposition
#check @originalPrimedBill_paid
#check @equation_5_21_extraction
#check @equation_5_27_original_conditional
#check @normalized_weight_literal
#check @single_nu_literal
#check @originalBaseScalar_literal
#check @lowCoefficient_half_literal
#check @originalPrimedBill_literal
#check @local_c1_parameter_domain
#check @local_c1_slot_unique
#check @equation_5_21_literal
#check @equation_5_23_literal

#print axioms originalCountFactor
#print axioms originalBaseScalar
#print axioms primedZeros
#print axioms primedSigma4
#print axioms selectedBill
#print axioms originalPrimedBill
#print axioms LocalC1Data
#print axioms LocalC1Data.mk
#print axioms LocalC1Data.selected_mem
#print axioms LocalC1Data.selected_right
#print axioms LocalC1Data.selected_real
#print axioms LocalC1Data.selected_simple
#print axioms LocalC1Data.selected_nonprincipal
#print axioms LocalC1Data.selected_real_character
#print axioms LocalC1Data.primitive_source
#print axioms LocalC1Data.region
#print axioms normalized_single_weight
#print axioms logNu_exp_sixth_antitone
#print axioms single_endpoint_log
#print axioms single_endpoint_nu
#print axioms single_endpoint_paid
#print axioms original_nu_single_scale
#print axioms equation_5_21_original
#print axioms original_base_endpoint
#print axioms original_base_global_decay
#print axioms originalBaseScalar_paid
#print axioms original_base_scalar_paid
#print axioms low_norm_ge_one
#print axioms source_six_low_main
#print axioms source_six_low_bound
#print axioms source_five_low_bound
#print axioms original_count_character
#print axioms original_count_family
#print axioms original_base_integral_cancellation
#print axioms original_low_beta_integral
#print axioms lowBetaBill_le_original_scalar
#print axioms equation_5_23_original
#print axioms rectangle_mem
#print axioms primed_right_boundary
#print axioms sigma4_exact_local_split
#print axioms selectedBill_paid
#print axioms actual_simple_lowKernel_original
#print axioms rectangle_upperMass
#print axioms primed_upperMass_le_family
#print axioms primedSigma4_le_original_bill
#print axioms original_finite_bill_decomposition
#print axioms originalPrimedBill_paid
#print axioms equation_5_21_extraction
#print axioms equation_5_27_original_conditional
#print axioms normalized_weight_literal
#print axioms single_nu_literal
#print axioms originalBaseScalar_literal
#print axioms lowCoefficient_half_literal
#print axioms originalPrimedBill_literal
#print axioms local_c1_parameter_domain
#print axioms local_c1_slot_unique
#print axioms equation_5_21_literal
#print axioms equation_5_23_literal

#check @LiuWang.Proof.DirichletZeroCount.Remainder.count_principal_le_sourceFive
#check @LiuWang.Proof.DirichletZeroCount.Remainder.count_nonprincipal_le_sourceSix_modulus
#print axioms LiuWang.Proof.DirichletZeroCount.Remainder.count_principal_le_sourceFive
#print axioms LiuWang.Proof.DirichletZeroCount.Remainder.count_nonprincipal_le_sourceSix_modulus
#check @Source524.equation_5_24_original_contribution
#check @Source525526.equation_5_25_original
#check @Source525526.equation_5_26_original
#print axioms Source524.equation_5_24_original_contribution
#print axioms Source525526.equation_5_25_original
#print axioms Source525526.equation_5_26_original
#print sourceNu
#print lowCoefficient
#print lowBetaBill
#print lowKernel
#print sigma4
#print rectangleZeros
#print DirichletZeroCount.zeroValues
#print DirichletZeroCount.count
#print familyCount
#print DirichletZeroCount.Remainder.sourceFiveBound
#print DirichletZeroCount.sourceSixBound

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
