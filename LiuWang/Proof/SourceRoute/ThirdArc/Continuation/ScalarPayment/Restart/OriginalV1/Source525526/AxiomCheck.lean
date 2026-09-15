import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.RealRemainder

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526

theorem scalar525_literal (L x : ℝ) :
    scalar525 L x =
      14000 * ((1 - (0.001 : ℝ) ^ (59 / 60 : ℝ)) / (59 / 60)) *
        L ^ (1 - x / 2) *
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L ^ x)) +
          2.50637 / Real.log (Real.log (L ^ x))) *
        Real.exp (-0.2067 * L / Real.log (10000 * Real.pi * L ^ x)) := rfl

theorem scalar526_literal (L x : ℝ) :
    scalar526 L x =
      2 * ((1 - (0.001 : ℝ) ^ (59 / 60 : ℝ)) / (59 / 60)) *
        L ^ (1 - x / 2) *
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L ^ x)) +
          2.50637 / Real.log (Real.log (L ^ x))) *
        Real.exp (-0.10367089 * L / Real.log (10000 * Real.pi * L ^ x)) := rfl

theorem originalLastBill_literal (N q : ℕ) [NeZero q] :
    originalLastBill N q =
      ((N : ℝ) * Real.sqrt q / q.totient) *
        ∫ alpha in (1 - 0.2067 / Real.log ((q : ℝ) * (10000 * Real.pi)))..
          (1 - 1 / (9.645908801 * Real.log ((q : ℝ) * (10000 * Real.pi)))),
          betaKernel N alpha * lowCoefficient alpha *
            familyCount q alpha (10000 * Real.pi) := rfl

theorem originalLastBill_and_lowStrip_literals {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    (((N : ℝ) * Real.sqrt q / q.totient) *
        (∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * lowHeight))..
          (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)),
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      (3 / 100000 : ℝ) * (N : ℝ) / sourceL N) ∧
    (((N : ℝ) * Real.sqrt q / q.totient) *
        (∫ alpha in (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight))..
          (1 - 1 / (9.645908801 * Real.log ((q : ℝ) * lowHeight))),
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      (3 / 100000 : ℝ) * (N : ℝ) / sourceL N) :=
  ⟨equation_5_25_original hN hq hq1 htotient, equation_5_26_original hN hq hq1 htotient⟩

#print originalScalar
#print axioms originalScalar
#print scalar525
#print axioms scalar525
#print scalar526
#print axioms scalar526
#print logScalar
#print axioms logScalar
#check @originalScalar_eq_logScalar
#print axioms originalScalar_eq_logScalar
#check @original_exponential_scaling
#print axioms original_exponential_scaling
#check @originalScalar_reduce_L
#print axioms originalScalar_reduce_L
#check @base_nu_bound
#print axioms base_nu_bound
#check @exponent525
#print axioms exponent525
#check @exponent526
#print axioms exponent526
#check @rational525
#print axioms rational525
#check @rational526
#print axioms rational526
#check @base_scalar_bound
#print axioms base_scalar_bound
#check @scalar525_paid
#print axioms scalar525_paid
#check @scalar526_paid
#print axioms scalar526_paid
#check @modulus_scalar
#print axioms modulus_scalar
#check @original_weight_le_scalar
#print axioms original_weight_le_scalar
#check @original_weight525_paid
#print axioms original_weight525_paid
#check @original_weight526_paid
#print axioms original_weight526_paid
#print lastLower
#print axioms lastLower
#print lastUpper
#print axioms lastUpper
#print originalLastBill
#print axioms originalLastBill
#check @last_interval_order
#print axioms last_interval_order
#check @theorem_two_low_domain
#print axioms theorem_two_low_domain
#check @strict_to_closed_count
#print axioms strict_to_closed_count
#check @original_T2_count
#print axioms original_T2_count
#check @original_last_integral_bound
#print axioms original_last_integral_bound
#check @lowStripBill_le_original_weight
#print axioms lowStripBill_le_original_weight
#check @equation_5_25_original
#print axioms equation_5_25_original
#check @originalLastBill_le_original_weight
#print axioms originalLastBill_le_original_weight
#check @equation_5_26_original
#print axioms equation_5_26_original
#print lastRealRemainder
#print axioms lastRealRemainder
#check @full_tail_split
#print axioms full_tail_split
#check @familyCount_above_c1_eq_real
#print axioms familyCount_above_c1_eq_real
#check @full_tail_eq_original_and_real
#print axioms full_tail_eq_original_and_real
#check @exceptionalTailBill_paid_with_real_remainder
#print axioms exceptionalTailBill_paid_with_real_remainder
#check @scalar525_literal
#print axioms scalar525_literal
#check @scalar526_literal
#print axioms scalar526_literal
#check @originalLastBill_literal
#print axioms originalLastBill_literal
#check @originalLastBill_and_lowStrip_literals
#print axioms originalLastBill_and_lowStrip_literals

#check @MultiZeroRepulsion.Continuation.general_theorem_two
#print axioms MultiZeroRepulsion.Continuation.general_theorem_two
#check @original_low_0478_subinterval
#print axioms original_low_0478_subinterval
#print lowStripBill
#print lowCoefficient
#print sourceNu
#print MultiZeroRepulsion.strictFamilyCount
#print familyCount
#print count

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526
