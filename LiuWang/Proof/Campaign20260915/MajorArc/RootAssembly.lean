import LiuWang.Proof.MinorArcEnergy.Ledger
import LiuWang.Proof.PrimePowerRemoval.Main
import LiuWang.Proof.MajorArcApproximation.Geometry

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ArcGeometry LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.MinorArcEnergy LiuWang.Proof.PrimePowerRemoval

namespace LiuWang.Proof.Campaign20260915.MajorArc

theorem minor_integrals_le_original_budget {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ +
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ +
      ‖∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        0.51 * (N : ℝ) ^ 2 := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hL : 0 < sourceL N := sourceL_pos hN'
  have hfourth :
      ‖∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.1743 * (N : ℝ) / sourceL N) *
          ∫ alpha in M4 N, ‖S N alpha‖ ^ 2 :=
    norm_setIntegral_le_local_energy N (measurableSet_M4 N) Set.sdiff_subset
      (fun _ ha => VaughanRecovery.M4_le_1743 hN ha)
  have hweight := weighted_energy_le_single_budget
    (B₂ := 0.4012 * (N : ℝ) / sourceL N)
    (B₃ := 0.5033 * (N : ℝ) / sourceL N)
    (B₄ := 0.1743 * (N : ℝ) / sourceL N)
    (B := 0.5033 * (N : ℝ) / sourceL N) hN' (by positivity)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)) hL.le)
    le_rfl
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)) hL.le)
  calc
    _ ≤ (0.5033 * (N : ℝ) / sourceL N) *
        ∫ alpha in sourceDomain N, ‖S N alpha‖ ^ 2 :=
      (add_le_add (add_le_add hsecond hthird) hfourth).trans hweight
    _ ≤ (0.5033 * (N : ℝ) / sourceL N) *
        (1.0012 * (N : ℝ) * Real.log N) :=
      mul_le_mul_of_nonneg_left (source_energy_le_sharp hN) (by positivity)
    _ = 0.50390396 * (N : ℝ) ^ 2 := by
      change _ / Real.log N * _ = _
      have hlog : Real.log N ≠ 0 := ne_of_gt hL
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)

theorem lambdaTripleCount_lower_of_original_arcs {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hmajor : 0.5437 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    (0.5437 - 0.51 : ℝ) * (N : ℝ) ^ 2 ≤ lambdaTripleCount N := by
  have hc := congrArg Complex.re
    (circleIntegral_fourArc (exp_2000_le_of_exp_3100_le hN))
  have h2 := Complex.re_le_norm
    (-(∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)))
  have h3 := Complex.re_le_norm
    (-(∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)))
  have h4 := Complex.re_le_norm
    (-(∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)))
  simp only [Complex.add_re, Complex.ofReal_re] at hc
  simp only [Complex.neg_re, norm_neg] at h2 h3 h4
  have hm := minor_integrals_le_original_budget hN hsecond hthird
  unfold majorIntegral at hmajor
  linarith

theorem threeOddPrimes_of_original_arcs {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hmajor : 0.5437 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N :=
  isThreeOddPrimeSum_of_lambda_lower_bound hN
    (lambdaTripleCount_lower_of_original_arcs hN hmajor hsecond hthird)

theorem theoremStatement_of_original_arcs
    (hmajor : ∀ N : ℕ, Odd N → Real.exp 3100 ≤ (N : ℝ) →
      0.5437 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re)
    (hsecond : ∀ N : ℕ, Odd N → Real.exp 3100 ≤ (N : ℝ) →
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird : ∀ N : ℕ, Odd N → Real.exp 3100 ≤ (N : ℝ) →
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.TheoremStatement := by
  intro N hodd hN
  exact threeOddPrimes_of_original_arcs hN
    (hmajor N hodd hN) (hsecond N hodd hN) (hthird N hodd hN)

#print axioms minor_integrals_le_original_budget
#print axioms theoremStatement_of_original_arcs

end LiuWang.Proof.Campaign20260915.MajorArc
