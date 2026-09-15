import LiuWang.Proof.WeightedLowZeros.Continuation.NearOne
import LiuWang.Proof.WeightedLowZeros.Continuation.BulkNumeric

/-! # Density counts after fixing the same actual source, with a paid bulk -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation

def retainedCount (q : ℕ) [NeZero q] (alpha y : ℝ)
    (d : PrimitiveQuadraticDatum) (e : ℂ) : ℕ :=
  ∑ chi : Character q, ∑ rho ∈ (retainedValues chi y d e).filter (fun rho => alpha ≤ rho.re),
    zeroMultiplicity chi rho

theorem familyCount_split_source {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (ha : 1/2 ≤ alpha)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e) :
    familyCount q alpha (x / q) = retainedCount q alpha (x / q) d e +
      if d.modulus ∣ q ∧ alpha ≤ e.re then 1 else 0 := by
  have h := sum_split_retained (q := q) (x / q) d e
    (fun chi rho => if alpha ≤ rho.re then zeroMultiplicity chi rho else 0)
  simp only [source_mem_iff hx hq hd, and_true] at h
  simp only [familyCount, count]
  simp only [Applications.values_eq_complete_filter _ ha, Finset.sum_filter,
    retainedCount, zeroMultiplicity] at h ⊢
  by_cases hdiv : d.modulus ∣ q
  · simp only [hdiv, if_true, true_and, show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from
      source_multiplicity hx hq hd hdiv] at h ⊢
    exact h
  · simpa only [hdiv, false_and, if_false, add_zero] using h

theorem retainedCount_zero_near {x alpha : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (ha : 1/2 ≤ alpha)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e)
    (hnear : regionCap x < alpha) :
    retainedCount q alpha (x / q) d e = 0 := by
  have hsplit := familyCount_split_source hx hq ha hd
  rw [near_familyCount_exact hx hq hd hnear] at hsplit
  omega

def retainedBand (N q : ℕ) [NeZero q] (y alpha beta : ℝ)
    (d : PrimitiveQuadraticDatum) (e : ℂ) : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (retainedValues chi y d e).filter (fun rho => alpha ≤ rho.re ∧ rho.re ≤ beta),
      (zeroMultiplicity chi rho : ℝ) * weight N rho.re

theorem retainedBand_le_count {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    (y alpha : ℝ) {beta : ℝ} (hb : 0 < beta) (d : PrimitiveQuadraticDatum) (e : ℂ) :
    retainedBand N q y alpha beta d e ≤
      weight N beta * retainedCount q alpha y d e := by
  unfold retainedBand retainedCount
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro chi _
  calc
    _ ≤ ∑ rho ∈ (retainedValues chi y d e).filter
        (fun rho => alpha ≤ rho.re ∧ rho.re ≤ beta),
          (zeroMultiplicity chi rho : ℝ) * weight N beta := by
      apply Finset.sum_le_sum
      intro rho hr
      obtain ⟨hr, _, hupper⟩ := Finset.mem_filter.mp hr
      have hz := CompleteExpansion.mem_zeroValues.mp (Finset.mem_filter.mp hr).1
      exact mul_le_mul_of_nonneg_left (weight_mono hN hz.2.1 hupper) (Nat.cast_nonneg _)
    _ ≤ ∑ rho ∈ (retainedValues chi y d e).filter (fun rho => alpha ≤ rho.re),
          (zeroMultiplicity chi rho : ℝ) * weight N beta := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro rho hr
        obtain ⟨hm, hl, _⟩ := Finset.mem_filter.mp hr
        exact Finset.mem_filter.mpr ⟨hm, hl⟩
      · exact fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (weight_nonneg N hb)
    _ = _ := by simp only [Nat.cast_sum, Finset.mul_sum, mul_comm]

theorem retainedBand_le_density {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    (y alpha : ℝ) {beta D : ℝ} (hb : 0 < beta)
    (d : PrimitiveQuadraticDatum) (e : ℂ)
    (hD : (retainedCount q alpha y d e : ℝ) ≤ D) :
    retainedBand N q y alpha beta d e ≤ weight N beta * D :=
  (retainedBand_le_count hN y alpha hb d e).trans
    (mul_le_mul_of_nonneg_left hD (weight_nonneg N hb))

def retainedTail (N q : ℕ) [NeZero q] (y alpha : ℝ)
    (d : PrimitiveQuadraticDatum) (e : ℂ) : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (retainedValues chi y d e).filter (fun rho => alpha < rho.re),
      (zeroMultiplicity chi rho : ℝ) * weight N rho.re

theorem retainedSum_le_bulk_add_tail (N q : ℕ) [NeZero q] (y alpha : ℝ)
    (d : PrimitiveQuadraticDatum) (e : ℂ) :
    retainedSum N q y d e ≤ bulkSum N q y alpha + retainedTail N q y alpha d e := by
  unfold retainedSum bulkSum retainedTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro chi _
  have hsplit := Finset.sum_filter_add_sum_filter_not (retainedValues chi y d e)
    (fun rho => rho.re ≤ alpha) (fun rho => (zeroMultiplicity chi rho : ℝ) * weight N rho.re)
  simp only [not_le] at hsplit
  rw [← hsplit]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hr, ha⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, ha⟩
  · intro rho hr _
    exact mul_nonneg (Nat.cast_nonneg _) (weight_nonneg N
      (CompleteExpansion.mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.1)

theorem retainedTail_eq_middle {N q : ℕ} [NeZero q] {x alpha : ℝ}
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e) :
    retainedTail N q (x / q) alpha d e =
      ∑ chi : Character q,
        ∑ rho ∈ (retainedValues chi (x / q) d e).filter
          (fun rho => alpha < rho.re ∧ rho.re ≤ regionCap x),
            (zeroMultiplicity chi rho : ℝ) * weight N rho.re := by
  unfold retainedTail
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  ext rho
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr, ha⟩
    exact ⟨hr, ha, retained_re_le hx hq hd chi hr⟩
  · exact fun h => ⟨h.1, h.2.1⟩

theorem retainedSum_numeric_bulk_and_middle {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e) :
    retainedSum N q (omegaCutoff N q) d e ≤ 6e-10 / sourceL N +
      ∑ chi : Character q,
        ∑ rho ∈ (retainedValues chi (omegaCutoff N q) d e).filter
          (fun rho => bulkCap N < rho.re ∧ rho.re ≤ regionCap (lowScale N)),
            (zeroMultiplicity chi rho : ℝ) * weight N rho.re := by
  obtain ⟨hx, hqx, he⟩ := lowScale_parameters hN hq
  have h := retainedSum_le_bulk_add_tail N q (omegaCutoff N q) (bulkCap N) d e
  have ht := retainedTail_eq_middle (N := N) (alpha := bulkCap N) hx hqx hd
  rw [he] at ht
  rw [ht] at h
  exact h.trans (add_le_add (source_bulk_numeric hN hq) le_rfl)

end LiuWang.Proof.WeightedLowZeros.Continuation
