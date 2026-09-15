import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.LocalCost
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.MotherTransport
import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def normalizedTotal (N r : ℕ) (beta : ℝ) (j : MixedKind) : ℝ :=
  ∑ q ∈ denominators (sourceP N), if r ∣ q then
    normalizedCost N q r beta (originalMotherBudget N q) j else 0

theorem originalMotherBudget_nonneg {N : ℕ} (hN : Real.exp 2000 ≤ (N:ℝ)) (q : ℕ) :
    0 ≤ originalMotherBudget N q := by
  have h := sourceL_pos hN
  unfold originalMotherBudget
  positivity

theorem selectedMixedCost_empty {N q : ℕ} [NeZero q]
    (hn : ∀ (chi : Character q) (rho : ℂ), rho ∉ exceptionalValues N chi)
    (j : MixedKind) : selectedMixedCost N q j = 0 := by
  have hz : ∀ chi : Character q, exceptionalValues N chi = ∅ :=
    fun chi => Finset.eq_empty_iff_forall_notMem.mpr (hn chi)
  simp [selectedMixedCost, NeZero.ne q, hz]

theorem common_source_normalization {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10/sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126*s/sourceL N^4) →
      ∀ j : MixedKind, totalMixedCost N j ≤ normalizedTotal N d.modulus rho.re j) := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hd, hdc, _, hz, hall⟩ := exceptionalValues_same_source hN' hq hr
  have hl : 0 < Real.log (sourceP N) :=
    Real.log_pos (by linarith [sourceP_ge_ten hN'])
  have hb : 1-1/(24*Real.log (sourceP N)) < rho.re := (Finset.mem_filter.mp hr).2.1
  have hdiv : 1/(24*Real.log (sourceP N)) ≤ 1/(9.645908801*Real.log (sourceP N)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hs : WeightedLowZeros.Continuation.PaperSource N d rho :=
    ⟨hd, hz, (exceptionalValues_quadratic_simple hN' hq hr).2.2.1,
      (CompleteExpansion.mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1,
      by linarith⟩
  refine ⟨d, hdc, hs, ?_⟩
  intro hlow hhigh j
  apply Finset.sum_le_sum
  intro s hs
  have hs' := (mem_denominators (sourceP_pos hN').le s).mp hs
  let : NeZero s := ⟨by omega⟩
  by_cases hex : ∃ (psi : Character s) (tau : ℂ), tau ∈ exceptionalValues N psi
  · obtain ⟨psi, tau, ht⟩ := hex
    obtain ⟨hte, hcon, hdiv, hind, _⟩ := hall s hs'.2 psi tau ht
    rw [if_pos hdiv, selectedMixedCost_at_witness hN' hs'.2 ht]
    have hm := original_mother_from_retained hN hs'.2 ht d hind
      (hte ▸ hlow s hs'.2 hdiv) (hhigh s hs'.2 hdiv)
    simpa only [hte, ← hcon, originalMotherBudget] using
      mixedCost_le_normalized hN' psi tau.re hm j
  · rw [selectedMixedCost_empty (by simpa only [not_exists] using hex)]
    split_ifs
    · exact normalizedCost_nonneg hN' hs'.1 _ (originalMotherBudget_nonneg hN' s) j
    · rfl

theorem common_source_normalized_integrals {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10/sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126*s/sourceL N^4) →
      ∀ j : MixedKind, ‖mixedIntegral N j‖ ≤ normalizedTotal N d.modulus rho.re j) := by
  obtain ⟨d, hdc, hs, h⟩ := common_source_normalization hN hq hr
  exact ⟨d, hdc, hs, fun hl hh j =>
    (actual_mixed_integrals (exp_2000_le_of_exp_3100_le hN) j).trans (h hl hh j)⟩

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
