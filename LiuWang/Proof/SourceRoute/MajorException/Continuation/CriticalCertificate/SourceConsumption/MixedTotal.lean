import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.MixedPayment
import LiuWang.Proof.SourceRoute.MajorException.AllInteractions

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

theorem phaseMass_principal_pruned {q : ℕ} [NeZero q] (N : ℕ) :
    phaseMass N (1 : Character q) =
      ∑ psi : Character q, if Nat.Coprime N psi.conductor then
        ‖phaseCoefficient N psi‖*‖gaussScale psi‖*regularMass N psi else 0 := by
  simp only [phaseMass, one_mul]
  apply Finset.sum_congr rfl
  intro psi _
  split_ifs with hc
  · rfl
  · have hz := congrArg norm (Frontier.Budget.gaussScale_mul_phase_non_coprime psi hc)
    simp only [norm_mul, norm_zero] at hz
    rw [mul_comm ‖phaseCoefficient N psi‖, hz, zero_mul]

theorem mixedCost_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (beta : ℝ) (j : MixedKind) :
    0 ≤ mixedCost N chi beta j := by
  have hp (psi : Character q) : 0 ≤ phaseMass N psi := by
    exact Finset.sum_nonneg (fun tau _ => mul_nonneg (by positivity) (regularMass_nonneg hN tau))
  have hpp : 0 ≤ pairPhaseMass N chi := by
    exact Finset.sum_nonneg (fun psi _ => Finset.sum_nonneg (fun tau _ =>
      mul_nonneg (mul_nonneg (by positivity) (regularMass_nonneg hN psi))
        (regularMass_nonneg hN tau)))
  obtain ⟨hj, he', hr'⟩ := roots_pos hN (NeZero.pos q)
  have he : 0 < exceptionalScale N beta :=
    mul_pos he' (baseWeight_pos (nat_pos_of_exp_le hN) _)
  have hp1 := hp (1 : Character q)
  have hpc := hp chi
  cases j <;> dsimp [mixedCost] <;> positivity

theorem mixedArc_no_exception {q : ℕ} [NeZero q] (N : ℕ)
    (hn : ∀ chi : Character q, exceptionalValues N chi = ∅) (j : MixedKind) :
    mixedArc N q j = 0 := by
  have he (eta : ℝ) : characterEvaluation (exceptionalCoefficient (q := q) N eta) = 0 := by
    funext a
    simp only [characterEvaluation, (no_exceptional_coefficient hn eta _).1,
      mul_zero, Finset.sum_const_zero, Pi.zero_apply]
  cases j <;> simp [mixedArc, mixedKernel, NeZero.ne q, he]

def selectedMixedCost (N q : ℕ) (j : MixedKind) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi, mixedCost N chi rho.re j

theorem selectedMixedCost_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (j : MixedKind) :
    selectedMixedCost N q j = mixedCost N chi rho.re j := by
  simp only [selectedMixedCost, dif_neg (NeZero.ne q)]
  rw [Fintype.sum_eq_single chi]
  · rw [exceptionalValues_at_witness hN hq hr, Finset.sum_singleton]
  · intro psi hp
    rw [exceptionalValues_other_character hN hq hr hp, Finset.sum_empty]

theorem selected_mixed_arc_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (j : MixedKind) :
    ‖mixedArc N q j‖ ≤ selectedMixedCost N q j := by
  by_cases hex : ∃ (chi : Character q) (rho : ℂ), rho ∈ exceptionalValues N chi
  · obtain ⟨chi, rho, hr⟩ := hex
    rw [selectedMixedCost_at_witness hN hq hr]
    exact actual_mixed_arc_bound hN hq hr j
  · have hn : ∀ chi : Character q, exceptionalValues N chi = ∅ :=
      fun chi => Finset.eq_empty_iff_forall_notMem.mpr (fun rho hr => hex ⟨chi, rho, hr⟩)
    rw [mixedArc_no_exception N hn]
    simp [selectedMixedCost, NeZero.ne q, hn]

theorem actual_mixed_totals {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (j : MixedKind) :
    (∑ q ∈ denominators (sourceP N), ‖mixedArc N q j‖) ≤
      ∑ q ∈ denominators (sourceP N), selectedMixedCost N q j := by
  apply Finset.sum_le_sum
  intro q hq
  have hq' := (mem_denominators (sourceP_pos hN).le q).mp hq
  let : NeZero q := ⟨by omega⟩
  exact selected_mixed_arc_bound hN hq'.2 j

theorem actual_mixed_integrals {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (j : MixedKind) :
    ‖mixedIntegral N j‖ ≤ ∑ q ∈ denominators (sourceP N), selectedMixedCost N q j :=
  (norm_sum_le _ _).trans (actual_mixed_totals hN j)

def datumMixedCost (N q : ℕ) (d : PrimitiveQuadraticDatum) (beta : ℝ) (j : MixedKind) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    if d.modulus ∣ q then mixedCost N (inducedAt d q) beta j else 0

theorem common_source_mixed_totals {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      ∀ j : MixedKind,
        (∑ s ∈ denominators (sourceP N), ‖mixedArc N s j‖) ≤
          ∑ s ∈ denominators (sourceP N), datumMixedCost N s d rho.re j := by
  obtain ⟨d, _, hdc, _, _, hall⟩ := exceptionalValues_same_source hN hq hr
  refine ⟨d, hdc, ?_⟩
  intro j
  apply Finset.sum_le_sum
  intro s hs
  have hs' := (mem_denominators (sourceP_pos hN).le s).mp hs
  let : NeZero s := ⟨by omega⟩
  simp only [datumMixedCost, dif_neg (NeZero.ne s)]
  by_cases hex : ∃ (psi : Character s) (tau : ℂ), tau ∈ exceptionalValues N psi
  · obtain ⟨psi, tau, ht⟩ := hex
    have hsrc := hall s hs'.2 psi tau ht
    rw [if_pos hsrc.2.2.1, hsrc.2.2.2.1, ← hsrc.1]
    exact actual_mixed_arc_bound hN hs'.2 ht j
  · have hn : ∀ psi : Character s, exceptionalValues N psi = ∅ :=
      fun psi => Finset.eq_empty_iff_forall_notMem.mpr (fun tau ht => hex ⟨psi, tau, ht⟩)
    rw [mixedArc_no_exception N hn, norm_zero]
    split_ifs
    · exact mixedCost_nonneg hN _ _ _
    · rfl

theorem common_source_mixed_integrals {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      ∀ j : MixedKind, ‖mixedIntegral N j‖ ≤
        ∑ s ∈ denominators (sourceP N), datumMixedCost N s d rho.re j := by
  obtain ⟨d, hdc, hall⟩ := common_source_mixed_totals hN hq hr
  exact ⟨d, hdc, fun j => (norm_sum_le _ _).trans (hall j)⟩

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
