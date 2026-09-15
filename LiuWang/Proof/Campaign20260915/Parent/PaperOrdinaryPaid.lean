import LiuWang.Proof.Campaign20260915.MajorArc.OrdinaryAudit
import LiuWang.Proof.Campaign20260915.MajorArc.PaperRoot
import LiuWang.Proof.Campaign20260915.HighSums.OriginalHighSum
import LiuWang.Proof.Campaign20260915.MajorArc.PaperPayment
import LiuWang.Proof.Campaign20260915.MajorArc.RootAssembly

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation

namespace LiuWang.Proof.Campaign20260915.Parent.PaperOrdinaryPaid

open LiuWang.Proof.Campaign20260915.MajorArc
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem threeOddPrimes_of_paper_source_budgets_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hT1 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hreal : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        ∀ (chi : Character q) (rho : ℂ), rho ∈ DirichletZeroCount.zeroValues chi 0 y →
          1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N := by
  apply threeOddPrimes_of_original_arcs hN _ hsecond hthird
  have hm := paper_caseII_ordinary_paid hN hodd hd h987 hphi
    (fun q _ hq => HighSums.highSum_original_of_T1_T7_near_one_real hN hq
      (hT1 q hq) (hT7 q hq) (hreal q hq))
  nlinarith [sq_nonneg (N : ℝ)]

#print axioms threeOddPrimes_of_paper_source_budgets_paid
end LiuWang.Proof.Campaign20260915.Parent.PaperOrdinaryPaid

#print axioms LiuWang.Proof.Campaign20260915.MajorArc.I13_with_third_head_paid
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.asymmetric_two_zero_contradiction
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.interactionIntegral_paper_source_split
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.lambdaTripleCount_lower_of_original_arcs
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.majorIntegral_paper_source_lower
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.minor_integrals_le_original_budget
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.noninducing_cap_019
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinaryBudgetPolynomial_bounds
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinaryMass_all_moduli
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinary_arc_all_moduli
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinary_budget_sum
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinary_kernel_moment_bound
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinary_major_lower_with_third_head_paid
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinary_polynomial_coarse
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.ordinary_scale_bound
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paperOrdinaryIntegral_norm_paid
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paperOrdinaryIntegral_signed_paid
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paper_caseII_of_original_ordinary
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paper_caseII_ordinary_paid
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paper_major_lower_with_ordinary
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paper_mixed_integrals_paid
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paper_pure_integrals_paid
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.paper_source_gap
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.retained_low_all_moduli
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.retained_tail_019
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.same_source_six_arcs_all_moduli
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.seed_019_upper
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.sixth_root_tangent
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.theoremStatement_of_original_arcs
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.third_finite_head
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.threeOddPrimes_of_low_high_and_minor
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.threeOddPrimes_of_original_arcs
#print axioms LiuWang.Proof.Campaign20260915.MajorArc.threeOddPrimes_of_paper_source
