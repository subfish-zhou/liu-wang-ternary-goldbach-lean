import LiuWang.Proof.SourceRoute.MajorException.SourceTotal
import LiuWang.Proof.SourceRoute.MajorException.MixedMoments

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException

def ordinaryKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let M := principalCoefficient q * J N eta
    let R := characterEvaluation (regularCoefficient (q := q) N eta) a;
    -3*M^2*R + 3*M*R^2 - R^3

theorem regularInteractionKernel_source_split (N a q : ℕ) (eta : ℝ) :
    regularInteractionKernel N a q eta =
      ordinaryKernel N a q eta +
        mixedKernel N a q eta .oneEach +
        mixedKernel N a q eta .oneExceptionalTwoRegular +
        mixedKernel N a q eta .twoExceptionalOneRegular := by
  by_cases hq : q = 0
  · simp [regularInteractionKernel, ordinaryKernel, mixedKernel, hq]
  · simp only [regularInteractionKernel, ordinaryKernel, mixedKernel, dif_neg hq]
    ring

theorem continuous_ordinaryKernel {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (ordinaryKernel N a q) := by
  by_cases hq : q = 0
  · subst q
    exact continuous_const
  let : NeZero q := ⟨hq⟩
  have hr : Continuous (fun eta =>
      characterEvaluation (regularCoefficient (q := q) N eta) a) :=
    continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_regularCoefficient hN chi))
  have hm : Continuous (fun eta => principalCoefficient q*J N eta) :=
    continuous_const.mul (continuous_J hN)
  unfold ordinaryKernel
  simp only [dif_neg hq]
  fun_prop

def ordinaryIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    ordinaryKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta

def mixedIntegral (N : ℕ) (j : MixedKind) : ℂ :=
  ∑ q ∈ denominators (sourceP N), mixedArc N q j

theorem mixedIntegral_eq_core (N : ℕ) (j : MixedKind) :
    mixedIntegral N j =
      ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
        mixedKernel N i.2 i.1 eta j * arcPhase N i.2 i.1 eta := by
  rw [coreIndices, Finset.sum_sigma]
  rfl

theorem regularInteractionIntegral_source_split {N : ℕ} (hN : 0 < N) :
    regularInteractionIntegral N =
      ordinaryIntegral N +
        mixedIntegral N .oneEach +
        mixedIntegral N .oneExceptionalTwoRegular +
        mixedIntegral N .twoExceptionalOneRegular := by
  simp only [mixedIntegral_eq_core, regularInteractionIntegral, ordinaryIntegral,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have ho : IntervalIntegrable (fun eta =>
      ordinaryKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
      volume (-deltaRadius N i.1) (deltaRadius N i.1) :=
    ((continuous_ordinaryKernel hN i.2 i.1).mul
      (continuous_arcPhase N i.2 i.1)).intervalIntegrable _ _
  have hm (j : MixedKind) : IntervalIntegrable (fun eta =>
      mixedKernel N i.2 i.1 eta j * arcPhase N i.2 i.1 eta)
      volume (-deltaRadius N i.1) (deltaRadius N i.1) :=
    ((continuous_mixedKernel hN i.2 i.1 j).mul
      (continuous_arcPhase N i.2 i.1)).intervalIntegrable _ _
  simp only [regularInteractionKernel_source_split, add_mul]
  rw [intervalIntegral.integral_add ((ho.add (hm .oneEach)).add (hm .oneExceptionalTwoRegular))
      (hm .twoExceptionalOneRegular),
    intervalIntegral.integral_add (ho.add (hm .oneEach)) (hm .oneExceptionalTwoRegular),
    intervalIntegral.integral_add ho (hm .oneEach)]

theorem interactionIntegral_source_split {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    interactionIntegral N =
      ordinaryIntegral N +
        selectedPureIntegral N .linear +
        mixedIntegral N .oneEach +
        mixedIntegral N .oneExceptionalTwoRegular +
        selectedPureIntegral N .quadratic +
        mixedIntegral N .twoExceptionalOneRegular +
        selectedPureIntegral N .cubic := by
  rw [interactionIntegral_exceptional_add_regular hN, exceptionalIntegral_eq_selected hN,
    regularInteractionIntegral_source_split (nat_pos_of_exp_le hN)]
  ring

theorem majorIntegral_source_lower {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.65617*(N : ℝ)^2 +
      (ordinaryIntegral N).re +
      (selectedPureIntegral N .linear).re +
      (mixedIntegral N .oneEach).re +
      (mixedIntegral N .oneExceptionalTwoRegular).re +
      (selectedPureIntegral N .quadratic).re +
      (mixedIntegral N .twoExceptionalOneRegular).re +
      (selectedPureIntegral N .cubic).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ (majorIntegral N).re := by
  have h := re_major_lower_strong hN hodd
  rw [interactionIntegral_source_split (exp_2000_le_of_exp_3100_le hN)] at h
  simp only [Complex.add_re] at h
  linarith

theorem cancelled_I19_reused {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
      Frontier.Budget.cancelledMixedKernel N a q eta * arcPhase N a q eta) = 0 :=
  Frontier.Budget.cancelledMixed_arc_zero hN hq

end LiuWang.Proof.SourceRoute.MajorException
