import LiuWang.Proof.WeightedLowZeros.Continuation.SourceComparison

/-!
# Actual low-modulus consequences of absence of the paper's wider source

No absence hypothesis at the larger R24 conductor range is needed. The proved
zero-free cap is still R24, not the unproved original c1 cap.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation

theorem no_paper_source_re_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), PaperSource N d e)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    rho.re ≤ regionCap (lowScale N) := by
  by_contra hc
  obtain ⟨d, _, hd, _, _⟩ := exists_paper_source_of_r24_mem hN hq hr (lt_of_not_ge hc)
  exact hnone ⟨d, rho, hd⟩

theorem no_paper_source_count_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), PaperSource N d e)
    {alpha : ℝ} (ha : regionCap (lowScale N) < alpha) (chi : Character q) :
    count chi alpha (omegaCutoff N q) = 0 := by
  obtain ⟨hx, _, he⟩ := lowScale_parameters hN hq
  have hset : zeroValues chi alpha (omegaCutoff N q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rho hr
    obtain ⟨hz, ⟨h0, h1, ht⟩, hb⟩ := mem_zeroValues.mp hr
    have hreg : RealClosure.region (lowScale N) q rho := ⟨ha.trans_le hb, by rwa [he]⟩
    have hfull := CompleteExpansion.mem_zeroValues.mpr
      ⟨hz, h0, h1, ht, (RealClosure.region_re_half hx hreg).le⟩
    exact (not_lt_of_ge (no_paper_source_re_le hN hq hnone hfull)) (ha.trans_le hb)
  simp only [count, hset, Finset.sum_empty]

theorem no_paper_source_familyCount_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), PaperSource N d e)
    {alpha : ℝ} (ha : regionCap (lowScale N) < alpha) :
    familyCount q alpha (omegaCutoff N q) = 0 := by
  simp only [familyCount, no_paper_source_count_zero hN hq hnone ha, Finset.sum_const_zero]

theorem no_paper_source_lowSum_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), PaperSource N d e)
    {padding : ℝ} (hp : 0 < padding) :
    lowSum N q ≤ weight N (regionCap (lowScale N)) *
      countMother q (omegaCutoff N q) padding := by
  obtain ⟨hx, _, _⟩ := lowScale_parameters hN hq
  unfold lowSum countMother
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro chi _
  exact subset_weighted_le (source_endpoint_ge_thousand hN) chi
    (le_trans (by norm_num) (omegaCutoff_ge (NeZero.pos q) hq)) hp (regionCap_pos hx)
    (CompleteExpansion.zeroValues chi (omegaCutoff N q)) (fun _ hr => hr)
    (fun _ hr => no_paper_source_re_le hN hq hnone hr)

end LiuWang.Proof.WeightedLowZeros.Continuation
