import LiuWang.Proof.WeightedLowZeros.Main

/-!
# Real-part slicing on the actual low-height values

The two-level bound leaves only the ordinary closed density count as input to
future refinements. The existing source-seven producer is used only on its
proved low-alpha and large-height domain; it is not extended to all low heights.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedLowZeros

def bulkSum (N q : ℕ) [NeZero q] (y alpha : ℝ) : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => rho.re ≤ alpha),
      (zeroMultiplicity chi rho : ℝ) * weight N rho.re

def tailSum (N q : ℕ) [NeZero q] (y alpha : ℝ) : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha < rho.re),
      (zeroMultiplicity chi rho : ℝ) * weight N rho.re

theorem sum_split_at (N q : ℕ) [NeZero q] (y alpha : ℝ) :
    (∑ chi : Character q, weightedSum N chi y) = bulkSum N q y alpha + tailSum N q y alpha := by
  unfold bulkSum tailSum weightedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro chi _
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not (CompleteExpansion.zeroValues chi y)
      (fun rho => rho.re ≤ alpha) (fun rho => (zeroMultiplicity chi rho : ℝ) * weight N rho.re)).symm

theorem bulkSum_le {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    {y a alpha : ℝ} (hy : 0 ≤ y) (ha : 0 < a) (halpha : 0 < alpha) :
    bulkSum N q y alpha ≤ weight N alpha * countMother q y a := by
  unfold bulkSum countMother
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro chi _
  exact subset_weighted_le hN chi hy ha halpha _ (Finset.filter_subset _ _)
    (fun _ hr => (Finset.mem_filter.mp hr).2)

theorem weightedSum_two_level {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    (chi : Character q) {y a alpha : ℝ} (hy : 0 ≤ y) (ha : 0 < a)
    (halpha : 1 / 2 ≤ alpha) (_halpha1 : alpha ≤ 1) :
    weightedSum N chi y ≤
      weight N alpha * sharpenedBound chi y a +
        (0.999 - weight N alpha) * count chi alpha y := by
  have hapos : 0 < alpha := by linarith
  have hpoint (rho : ℂ) (hr : rho ∈ CompleteExpansion.zeroValues chi y) :
      weight N rho.re ≤ weight N alpha + if alpha ≤ rho.re then 0.999 - weight N alpha else 0 := by
    have hm := CompleteExpansion.mem_zeroValues.mp hr
    by_cases h : alpha ≤ rho.re
    · rw [if_pos h]
      linarith [weight_le_one hN hm.2.1 hm.2.2.1.le]
    · rw [if_neg h, add_zero]
      exact weight_mono hN hm.2.1 (le_of_not_ge h)
  calc
    _ ≤ ∑ rho ∈ CompleteExpansion.zeroValues chi y, (zeroMultiplicity chi rho : ℝ) *
        (weight N alpha + if alpha ≤ rho.re then 0.999 - weight N alpha else 0) :=
      Finset.sum_le_sum fun rho hr =>
        mul_le_mul_of_nonneg_left (hpoint rho hr) (Nat.cast_nonneg _)
    _ = weight N alpha * count chi (1 / 2) y +
        (0.999 - weight N alpha) * count chi alpha y := by
      rw [Applications.count_half_eq_complete, count, Applications.values_eq_complete_filter _ halpha]
      simp only [Nat.cast_sum, Finset.mul_sum, Finset.sum_filter, zeroMultiplicity,
        mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
      congr 1
      · apply Finset.sum_congr rfl
        intro _ _
        ring
      · apply Finset.sum_congr rfl
        intro _ _
        split_ifs <;> ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (count_le_sharpenedBound chi (1 / 2) hy ha)
        (weight_nonneg N hapos)) le_rfl

theorem family_two_level {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    {y a alpha : ℝ} (hy : 0 ≤ y) (ha : 0 < a)
    (halpha : 1 / 2 ≤ alpha) (halpha1 : alpha ≤ 1) :
    (∑ chi : Character q, weightedSum N chi y) ≤ weight N alpha * countMother q y a +
      (0.999 - weight N alpha) * familyCount q alpha y := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => weightedSum_two_level hN chi hy ha halpha halpha1)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, countMother, familyCount,
    Nat.cast_sum] using h

theorem family_two_level_of_density {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    {y a alpha D : ℝ} (hy : 0 ≤ y) (ha : 0 < a)
    (halpha : 1 / 2 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hD : (familyCount q alpha y : ℝ) ≤ D) :
    (∑ chi : Character q, weightedSum N chi y) ≤ weight N alpha * countMother q y a +
      (0.999 - weight N alpha) * D := by
  apply (family_two_level hN hy ha halpha halpha1).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hD
    (sub_nonneg.mpr (weight_le_one hN (by linarith) halpha1)))

theorem family_two_level_sourceSeven_low {N q : ℕ} [NeZero q]
    (hN : 1000 ≤ (N : ℝ)) {y a alpha : ℝ} (hy : 10000 ≤ y) (ha : 0 < a)
    (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 2 / 3) :
    (∑ chi : Character q, weightedSum N chi y) ≤ weight N alpha * countMother q y a +
      (0.999 - weight N alpha) * min (countMother q y a) (Applications.sourceSevenBound q alpha y) :=
  family_two_level_of_density hN (by linarith) ha halpha (by linarith)
    (le_min (familyCount_le_sharpened q alpha (by linarith) ha)
      (Applications.familyCount_le_sourceSeven_low q hy halpha halpha'))

theorem lowSum_two_level {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {a alpha : ℝ} (ha : 0 < a) (halpha : 1 / 2 ≤ alpha) (halpha1 : alpha ≤ 1) :
    lowSum N q ≤ weight N alpha * countMother q (omegaCutoff N q) a +
      (0.999 - weight N alpha) * familyCount q alpha (omegaCutoff N q) :=
  family_two_level (source_endpoint_ge_thousand hN)
    (le_trans (by norm_num) (Parameters.omegaCutoff_ge (NeZero.pos q) hq)) ha halpha halpha1

end LiuWang.Proof.WeightedLowZeros
