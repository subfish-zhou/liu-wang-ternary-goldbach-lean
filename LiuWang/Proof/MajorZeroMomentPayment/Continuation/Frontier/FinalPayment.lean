import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.TotientSeven

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

theorem conductorPolynomial_mono (d : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    conductorPolynomial d u ≤ conductorPolynomial d v := by
  unfold conductorPolynomial
  gcongr

def sharpConductorCost (N d : ℕ) (beta : ℝ) : ℝ :=
  6.69*(N : ℝ)^2 *
    conductorPolynomial d (1.02*baseWeight N beta)/(d.totient : ℝ)^2

theorem fixed_source_absolute_total_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      (∑ s ∈ denominators (sourceP N), ‖exceptionalArc N s‖) ≤
        sharpConductorCost N d.modulus rho.re := by
  obtain ⟨d, _, hdc, _, _, hall⟩ := exceptionalValues_same_source hN hq hr
  refine ⟨d, hdc, ?_⟩
  have hd : 0 < d.modulus := by rw [hdc]; exact Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hu : 0 ≤ realEndpoint N rho.re := by unfold realEndpoint; positivity
  have huv : realEndpoint N rho.re ≤ 1.02*baseWeight N rho.re := by
    have h := exceptional_endpointGap_small hN hr
    unfold endpointGap at h
    linarith
  let V := conductorPolynomial d.modulus (1.02*baseWeight N rho.re)
  have hV : 0 ≤ V := conductorPolynomial_nonneg _ (by unfold baseWeight; positivity)
  let K := (3/Real.pi)*(N : ℝ)^2*V
  have hK : 0 ≤ K := mul_nonneg (by positivity) hV
  have hlocal (s : ℕ) (hs : s ∈ denominators (sourceP N)) :
      ‖exceptionalArc N s‖ ≤ K * (if d.modulus ∣ s then 1/(s.totient : ℝ)^2 else 0) := by
    have hs' := (mem_denominators (sourceP_pos hN).le s).mp hs
    let : NeZero s := ⟨by omega⟩
    by_cases hex : ∃ (psi : Character s) (tau : ℂ), tau ∈ exceptionalValues N psi
    · obtain ⟨psi, tau, ht⟩ := hex
      have hsrc := hall s hs'.2 psi tau ht
      have hb := exceptionalArc_norm_conductor hN hs'.2 ht
      rw [hsrc.1, ← hsrc.2.1] at hb
      rw [if_pos hsrc.2.2.1]
      apply hb.trans
      have hm := conductorPolynomial_mono d.modulus hu huv
      calc
        _ ≤ (3/Real.pi)*(N : ℝ)^2*V/(s.totient : ℝ)^2 := by gcongr
        _ = _ := by dsimp [K]; ring
    · have hn : ∀ psi : Character s, exceptionalValues N psi = ∅ := by
        intro psi
        exact Finset.eq_empty_iff_forall_notMem.mpr (fun tau ht => hex ⟨psi, tau, ht⟩)
      rw [(exceptionalArc_no_exception N hn).1, norm_zero]
      split_ifs <;> positivity
  apply (Finset.sum_le_sum hlocal).trans
  rw [← Finset.mul_sum]
  have hm := mul_le_mul_of_nonneg_left
    (reciprocal_totient_multiples_seven ⌊sourceP N⌋₊ hd) hK
  apply hm.trans
  have hc : (21 : ℝ)/Real.pi ≤ 6.69 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_d4]
  calc
    _ = (21/Real.pi)*(N : ℝ)^2*V/(d.modulus.totient : ℝ)^2 := by dsimp [K]; ring
    _ ≤ _ := by unfold sharpConductorCost; gcongr

theorem exceptionalIntegral_paid_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      max (totalAllModuliExceptionalPayment N) (-sharpConductorCost N d.modulus rho.re) ≤
        (exceptionalIntegral N).re := by
  obtain ⟨d, hd, hb⟩ := fixed_source_absolute_total_sharp hN hq hr
  refine ⟨d, hd, max_le (exceptionalIntegral_allModuli_payment hN) ?_⟩
  have he : exceptionalIntegral N = ∑ s ∈ denominators (sourceP N), exceptionalArc N s := by
    rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
    rfl
  have hn : ‖exceptionalIntegral N‖ ≤ sharpConductorCost N d.modulus rho.re := by
    rw [he]
    exact (norm_sum_le _ _).trans hb
  have h := Complex.re_le_norm (-exceptionalIntegral N)
  rw [Complex.neg_re, norm_neg] at h
  linarith

theorem lambdaTripleCount_sharp_direct {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      0.48166084*(N : ℝ)^2 +
        max (totalAllModuliExceptionalPayment N) (-sharpConductorCost N d.modulus rho.re) +
        totalEnhancedRegularPayment N + (regularHigherIntegral N).re +
        (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
        (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
        6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hd, hb⟩ := exceptionalIntegral_paid_sharp hN' hq hr
  refine ⟨d, hd, ?_⟩
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re] at h
  linarith [enhancedPayment_integral hN']

theorem exceptionalIntegral_none {N : ℕ}
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    exceptionalIntegral N = 0 := by
  have he : exceptionalIntegral N = ∑ s ∈ denominators (sourceP N), exceptionalArc N s := by
    rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
    rfl
  rw [he]
  apply Finset.sum_eq_zero
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact (exceptionalArc_no_exception N (hnone q hq)).1

theorem lambdaTripleCount_no_exception_direct {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    0.48166084*(N : ℝ)^2 +
      totalEnhancedRegularPayment N + (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re, exceptionalIntegral_none hnone,
    Complex.zero_re] at h
  linarith [enhancedPayment_integral hN']

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier
