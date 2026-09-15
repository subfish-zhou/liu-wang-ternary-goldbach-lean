import LiuWang.Proof.WeightedLowZeros.Deletion
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Strong

/-! # Ordinary multiplicity counts strictly inside the frozen zero regions -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation

theorem near_values_iff {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e)
    (ha : regionCap x < alpha) (chi : Character q) (rho : ℂ) :
    rho ∈ zeroValues chi alpha (x / q) ↔
      d.modulus ∣ q ∧ chi = inducedAt d q ∧ rho = e ∧ alpha ≤ e.re := by
  constructor
  · intro hr
    obtain ⟨hz, ⟨_, h1, ht⟩, hb⟩ := mem_zeroValues.mp hr
    have hp : chi ≠ 1 ∨ rho ≠ 1 := Or.inr (fun h => by simp [h] at h1)
    obtain ⟨he, _, hdq, hc, _⟩ :=
      source_controls hx hd q hq chi rho ⟨ha.trans_le hb, ht⟩ hp hz
    exact ⟨hdq, hc.symm, he, he ▸ hb⟩
  · rintro ⟨hdq, hc, rfl, hb⟩
    have hm := CompleteExpansion.mem_zeroValues.mp
      ((source_mem_iff hx hq hd chi).mpr ⟨hdq, hc⟩)
    exact mem_zeroValues.mpr ⟨hm.1, ⟨hm.2.1, hm.2.2.1, hm.2.2.2.1⟩, hb⟩

theorem near_count_exact {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e)
    (ha : regionCap x < alpha) (chi : Character q) :
    count chi alpha (x / q) =
      if d.modulus ∣ q ∧ chi = inducedAt d q ∧ alpha ≤ e.re then 1 else 0 := by
  have hset : zeroValues chi alpha (x / q) =
      if d.modulus ∣ q ∧ chi = inducedAt d q ∧ alpha ≤ e.re then {e} else ∅ := by
    ext rho
    rw [near_values_iff hx hq hd ha]
    split_ifs <;> simp_all only [Finset.mem_singleton, Finset.notMem_empty]
    all_goals tauto
  rw [count, hset]
  split_ifs with h
  · simp only [Finset.sum_singleton]
    rw [h.2.1]
    exact source_multiplicity hx hq hd h.1
  · exact Finset.sum_empty

theorem near_familyCount_exact {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e)
    (ha : regionCap x < alpha) :
    familyCount q alpha (x / q) = if d.modulus ∣ q ∧ alpha ≤ e.re then 1 else 0 := by
  unfold familyCount
  simp_rw [near_count_exact hx hq hd ha]
  by_cases hdq : d.modulus ∣ q
  · by_cases hb : alpha ≤ e.re <;> simp [hdq, hb]
  · simp [hdq]

theorem near_count_zero_of_no_source {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (ha : regionCap x < alpha)
    (hnone : ¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), SourceAt x d e)
    (chi : Character q) : count chi alpha (x / q) = 0 := by
  have hset : zeroValues chi alpha (x / q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rho hr
    obtain ⟨hz, ⟨h0, h1, ht⟩, hb⟩ := mem_zeroValues.mp hr
    have hreg : RealClosure.region x q rho := ⟨ha.trans_le hb, ht⟩
    have hfull := CompleteExpansion.mem_zeroValues.mpr
      ⟨hz, h0, h1, ht, (RealClosure.region_re_half hx hreg).le⟩
    obtain ⟨d, hd⟩ := exists_source_of_mem hx hq hfull (ha.trans_le hb)
    exact hnone ⟨d, rho, hd⟩
  simp only [count, hset, Finset.sum_empty]

theorem near_familyCount_zero_of_no_source {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (ha : regionCap x < alpha)
    (hnone : ¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), SourceAt x d e) :
    familyCount q alpha (x / q) = 0 := by
  simp only [familyCount, near_count_zero_of_no_source hx hq ha hnone, Finset.sum_const_zero]

theorem primitive_powers_count_zero {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : Character q)
    (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (hc2 : chi^2 ≠ 1) (hp2 : (chi^2).IsPrimitive)
    (hc3 : chi^3 ≠ 1) (hp3 : (chi^3).IsPrimitive)
    (hc4 : chi^4 ≠ 1) (hp4 : (chi^4).IsPrimitive)
    (ha : 1 - 1 / ((193 / 20) * Real.log x) < alpha) :
    count chi alpha (x / q) = 0 := by
  have hset : zeroValues chi alpha (x / q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rho hr
    obtain ⟨hz, ⟨_, _, ht⟩, hb⟩ := mem_zeroValues.mp hr
    exact RealClosure.quartic_primitive_powers_no_zero_193_20 hx hq chi
      hc hp hc2 hp2 hc3 hp3 hc4 hp4 (ha.trans_le hb) ht hz
  simp only [count, hset, Finset.sum_empty]

end LiuWang.Proof.WeightedLowZeros.Continuation
