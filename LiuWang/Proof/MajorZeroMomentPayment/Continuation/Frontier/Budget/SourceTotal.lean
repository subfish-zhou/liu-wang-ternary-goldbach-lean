import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.SourcePhase

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget

def quadraticSourceCost (N r : ℕ) (beta : ℝ) : ℝ :=
  20.07*(N : ℝ)^2*(r : ℝ)*(1.02*baseWeight N beta)^2/(r.totient : ℝ)^2

def sourceCost (N r : ℕ) (beta : ℝ) : ℝ :=
  if Nat.Coprime N r then sharpConductorCost N r beta else quadraticSourceCost N r beta

theorem sourceCost_le_sharp (N r : ℕ) (beta : ℝ) :
    sourceCost N r beta ≤ sharpConductorCost N r beta := by
  unfold sourceCost
  split_ifs
  · rfl
  · unfold quadraticSourceCost sharpConductorCost conductorPolynomial
    have hv : 0 ≤ 1.02*baseWeight N beta := by unfold baseWeight; positivity
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_nonneg (by positivity : 0 ≤ 6.69*(N : ℝ)^2)
      (by positivity : 0 ≤ 3*Real.sqrt (r : ℝ)*(1.02*baseWeight N beta) +
        (r : ℝ)*Real.sqrt r*(1.02*baseWeight N beta)^3)]

theorem fixed_source_non_coprime_total {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hnc : ¬ Nat.Coprime N chi.conductor) :
    (∑ s ∈ denominators (sourceP N), ‖exceptionalArc N s‖) ≤
      quadraticSourceCost N chi.conductor rho.re := by
  obtain ⟨d, _, hdc, _, _, hall⟩ := exceptionalValues_same_source hN hq hr
  have hd : 0 < d.modulus := by rw [hdc]; exact Nat.pos_of_ne_zero chi.conductor_ne_zero
  have huv : realEndpoint N rho.re ≤ 1.02*baseWeight N rho.re := by
    have h := exceptional_endpointGap_small hN hr
    unfold endpointGap at h
    linarith
  have hu : 0 ≤ realEndpoint N rho.re := by unfold realEndpoint; positivity
  let K := (9/Real.pi)*(N : ℝ)^2*(d.modulus : ℝ)*(1.02*baseWeight N rho.re)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlocal (s : ℕ) (hs : s ∈ denominators (sourceP N)) :
      ‖exceptionalArc N s‖ ≤ K*(if d.modulus ∣ s then 1/(s.totient : ℝ)^2 else 0) := by
    have hs' := (mem_denominators (sourceP_pos hN).le s).mp hs
    let : NeZero s := ⟨by omega⟩
    by_cases hex : ∃ (psi : Character s) (tau : ℂ), tau ∈ exceptionalValues N psi
    · obtain ⟨psi, tau, ht⟩ := hex
      have he := hall s hs'.2 psi tau ht
      have hn : ¬ Nat.Coprime N psi.conductor := by rwa [← he.2.1, hdc]
      have hb := exceptionalArc_non_coprime_norm hN hs'.2 ht hn
      rw [he.1, ← he.2.1] at hb
      rw [if_pos he.2.2.1]
      apply hb.trans
      calc
        _ ≤ K/(s.totient : ℝ)^2 := by dsimp [K]; gcongr
        _ = _ := by ring
    · have hn : ∀ psi : Character s, exceptionalValues N psi = ∅ :=
        fun psi => Finset.eq_empty_iff_forall_notMem.mpr (fun tau ht => hex ⟨psi, tau, ht⟩)
      rw [(exceptionalArc_no_exception N hn).1, norm_zero]
      split_ifs <;> positivity
  apply (Finset.sum_le_sum hlocal).trans
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left
    (reciprocal_totient_multiples_seven ⌊sourceP N⌋₊ hd) hK).trans
  have hc : (63 : ℝ)/Real.pi ≤ 20.07 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_d4]
  calc
    _ = (63/Real.pi)*(N : ℝ)^2*(d.modulus : ℝ)*
        (1.02*baseWeight N rho.re)^2/(d.modulus.totient : ℝ)^2 := by dsimp [K]; ring
    _ ≤ quadraticSourceCost N d.modulus rho.re := by unfold quadraticSourceCost; gcongr
    _ = _ := by rw [hdc]

theorem fixed_source_total {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    (∑ s ∈ denominators (sourceP N), ‖exceptionalArc N s‖) ≤
      sourceCost N chi.conductor rho.re := by
  unfold sourceCost
  split_ifs with hc
  · obtain ⟨d, hd, hb⟩ := fixed_source_absolute_total_sharp hN hq hr
    rwa [hd] at hb
  · exact fixed_source_non_coprime_total hN hq hr hc

theorem exceptionalIntegral_paid_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    max (totalAllModuliExceptionalPayment N) (-sourceCost N chi.conductor rho.re) ≤
      (exceptionalIntegral N).re := by
  apply max_le (exceptionalIntegral_allModuli_payment hN)
  have he : exceptionalIntegral N = ∑ s ∈ denominators (sourceP N), exceptionalArc N s := by
    rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
    rfl
  have hn : ‖exceptionalIntegral N‖ ≤ sourceCost N chi.conductor rho.re := by
    rw [he]
    exact (norm_sum_le _ _).trans (fixed_source_total hN hq hr)
  have h := Complex.re_le_norm (-exceptionalIntegral N)
  rw [Complex.neg_re, norm_neg] at h
  linarith

theorem lambdaTripleCount_source_direct {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    0.48166084*(N : ℝ)^2 +
      max (totalAllModuliExceptionalPayment N) (-sourceCost N chi.conductor rho.re) +
      totalEnhancedRegularPayment N + (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re] at h
  linarith [enhancedPayment_integral hN', exceptionalIntegral_paid_source hN' hq hr]

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget
