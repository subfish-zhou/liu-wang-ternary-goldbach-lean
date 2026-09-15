import LiuWang.Proof.SourceRoute.Exception.Restart.PaperApplication
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.NoExceptionAssembly

/-! Exact closed short-window classification in the existing PaperSource branch.
This does not assert that a PaperSource exists or classify the source-free branch.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.LowSum
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem short_zero_iff_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (chi : Character q) {rho : ℂ} :
    (rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) ∧
      |rho.im| ≤ sourceP N / q ∧ paperCap N ≤ rho.re) ↔
        d.modulus ∣ q ∧ chi = inducedAt d q ∧ rho = e := by
  constructor
  · rintro ⟨hr, ht, hb⟩
    have hm := CompleteExpansion.mem_zeroValues.mp hr
    have hpole : chi ≠ 1 ∨ rho ≠ 1 :=
      Or.inr (fun he => CompleteExpansion.zeroValues_pole_excluded chi _ (he ▸ hr))
    exact (SourceRoute.Exception.Restart.paper_source_original_zero_iff
      hN hq hd chi hb ht hpole).mp hm.1
  · rintro ⟨hdiv, rfl, rfl⟩
    refine ⟨(paper_induced_mem_iff hN hq hd).mpr hdiv, ?_, hd.2.2.2.2.le⟩
    rw [hd.2.2.1, abs_zero]
    exact div_nonneg (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le
      (Nat.cast_nonneg q)

theorem short_absence_iff_not_dvd {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    (∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N) ↔ ¬d.modulus ∣ q := by
  constructor
  · intro hshort hdiv
    obtain ⟨hr, ht, hb⟩ :=
      (short_zero_iff_source hN hq hd (inducedAt d q)).mpr ⟨hdiv, rfl, rfl⟩
    exact (not_lt_of_ge hb) (hshort _ _ hr ht)
  · intro hdiv chi rho hr ht
    exact lt_of_not_ge (fun hb =>
      hdiv ((short_zero_iff_source hN hq hd chi).mp ⟨hr, ht, hb⟩).1)

theorem short_absence_of_not_dvd {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : ¬d.modulus ∣ q) :
    ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N :=
  (short_absence_iff_not_dvd hN hq hd).mpr hdiv

theorem short_window_filter_eq {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (chi : Character q) :
    (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
      (fun rho => |rho.im| ≤ sourceP N / q ∧ paperCap N ≤ rho.re) =
        if d.modulus ∣ q ∧ chi = inducedAt d q then {e} else ∅ := by
  ext rho
  simp only [Finset.mem_filter]
  rw [short_zero_iff_source hN hq hd chi]
  by_cases hc : d.modulus ∣ q ∧ chi = inducedAt d q
  · simp only [if_pos hc, Finset.mem_singleton]
    exact ⟨fun h => h.2.2, fun h => ⟨hc.1, hc.2, h⟩⟩
  · simp only [if_neg hc, Finset.notMem_empty, iff_false]
    exact fun h => hc ⟨h.1, h.2.1⟩

theorem short_window_multiplicity_sum {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (chi : Character q) :
    (∑ rho ∈ (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
      (fun rho => |rho.im| ≤ sourceP N / q ∧ paperCap N ≤ rho.re),
        zeroMultiplicity chi rho) =
      if d.modulus ∣ q ∧ chi = inducedAt d q then 1 else 0 := by
  rw [short_window_filter_eq hN hq hd chi]
  by_cases hc : d.modulus ∣ q ∧ chi = inducedAt d q
  · simp only [if_pos hc, Finset.sum_singleton]
    rw [hc.2]
    exact paper_source_multiplicity hN hd hc.1
  · simp only [if_neg hc, Finset.sum_empty]

theorem high_seed_nonreal_of_not_dvd {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : ¬d.modulus ∣ q) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hb : paperCap N ≤ rho.re) :
    sourceP N / q < |rho.im| ∧ rho.im ≠ 0 :=
  original_high_seed_nonreal hN (short_absence_of_not_dvd hN hq hd hdiv) hr hb

end LiuWang.Proof.Campaign20260915.OriginalRegion
