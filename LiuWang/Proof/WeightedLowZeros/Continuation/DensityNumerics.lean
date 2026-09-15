import LiuWang.Proof.WeightedLowZeros.Continuation.RetainedDensity
import LiuWang.Proof.WeightedLowZeros.Continuation.TailBudget

/-!
# Sufficient ordinary density branches for the two original numerical budgets

The numerical implications are proved here. The displayed low-level density
counts and pointwise upper region are inputs, not asserted source producers.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation

def cutCount (q : ℕ) [NeZero q] (Z : Character q → Finset ℂ) (alpha : ℝ) : ℕ :=
  ∑ chi : Character q, ∑ rho ∈ (Z chi).filter (fun rho => alpha ≤ rho.re),
    zeroMultiplicity chi rho

def cutMass (N q : ℕ) [NeZero q] (Z : Character q → Finset ℂ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℝ) * weight N rho.re

theorem cutMass_le_three_steps {N q : ℕ} [NeZero q]
    (hN : 1000 ≤ (N : ℝ)) (y b a t : ℝ) (ha : 0 < a) (ht : 0 < t)
    (Z : Character q → Finset ℂ) (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi y)
    (hupper : ∀ chi rho, rho ∈ Z chi → rho.re ≤ t) :
    cutMass N q Z ≤ bulkSum N q y b +
      weight N a * cutCount q Z b + weight N t * cutCount q Z a := by
  have hpoint (chi : Character q) (rho : ℂ) (hr : rho ∈ Z chi) :
      (zeroMultiplicity chi rho : ℝ) * weight N rho.re ≤
        (if rho.re ≤ b then (zeroMultiplicity chi rho : ℝ) * weight N rho.re else 0) +
        weight N a * (if b ≤ rho.re then (zeroMultiplicity chi rho : ℝ) else 0) +
        weight N t * (if a ≤ rho.re then (zeroMultiplicity chi rho : ℝ) else 0) := by
    have hm : (0 : ℝ) ≤ zeroMultiplicity chi rho := Nat.cast_nonneg _
    have ha0 := weight_nonneg N ha
    have ht0 := weight_nonneg N ht
    have hr0 := (CompleteExpansion.mem_zeroValues.mp (hZ chi hr)).2.1
    by_cases hb : rho.re ≤ b
    · simp only [if_pos hb]
      split_ifs <;> nlinarith
    · by_cases hab : rho.re ≤ a
      · have hw := mul_le_mul_of_nonneg_left (weight_mono hN hr0 hab) hm
        simp only [if_neg hb, if_pos (le_of_not_ge hb), zero_add]
        split_ifs <;> nlinarith
      · have hw := mul_le_mul_of_nonneg_left (weight_mono hN hr0 (hupper chi rho hr)) hm
        simp only [if_neg hb, if_pos (le_of_not_ge hb), if_pos (le_of_not_ge hab), zero_add]
        nlinarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => Finset.sum_le_sum (s := Z chi) (fun rho hr => hpoint chi rho hr))
  have hbulk :
      (∑ chi : Character q, ∑ rho ∈ Z chi,
        if rho.re ≤ b then (zeroMultiplicity chi rho : ℝ) * weight N rho.re else 0) ≤
          bulkSum N q y b := by
    simp only [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro chi _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hr
      obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hZ chi hr, hb⟩
    · intro rho hr _
      exact mul_nonneg (Nat.cast_nonneg _) (weight_nonneg N
        (CompleteExpansion.mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.1)
  have hcast (p : Prop) (n : ℕ) :
      ((if p then n else 0 : ℕ) : ℝ) = if p then (n : ℝ) else 0 := by
    split_ifs <;> simp
  simp only [cutMass, cutCount, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter,
    Finset.sum_add_distrib, hcast] at hsum ⊢
  exact hsum.trans (add_le_add (add_le_add hbulk le_rfl) le_rfl)

theorem cutMass_partition (N q : ℕ) [NeZero q] (Z : Character q → Finset ℂ) (a : ℝ) :
    cutMass N q Z =
      cutMass N q (fun chi => (Z chi).filter (fun rho => rho.re ≤ a)) +
      cutMass N q (fun chi => (Z chi).filter (fun rho => a < rho.re)) := by
  unfold cutMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro chi _
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not (Z chi) (fun rho => rho.re ≤ a)
      (fun rho => (zeroMultiplicity chi rho : ℝ) * weight N rho.re)).symm

theorem cutMass_le_count {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    (y a : ℝ) {t : ℝ} (_ht : 0 < t) (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi y)
    (hlower : ∀ chi rho, rho ∈ Z chi → a ≤ rho.re)
    (hupper : ∀ chi rho, rho ∈ Z chi → rho.re ≤ t) :
    cutMass N q Z ≤ weight N t * cutCount q Z a := by
  have hfilter (chi : Character q) : (Z chi).filter (fun rho => a ≤ rho.re) = Z chi :=
    Finset.filter_eq_self.mpr (hlower chi)
  unfold cutMass cutCount
  simp only [hfilter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum
  intro rho hr
  have h := mul_le_mul_of_nonneg_left
    (weight_mono hN (CompleteExpansion.mem_zeroValues.mp (hZ chi hr)).2.1 (hupper chi rho hr))
    (Nat.cast_nonneg (zeroMultiplicity chi rho) : (0 : ℝ) ≤ zeroMultiplicity chi rho)
  simpa only [mul_comm] using h

theorem cutCount_mono {q : ℕ} [NeZero q] (Z W : Character q → Finset ℂ)
    (hZW : ∀ chi, Z chi ⊆ W chi) (a : ℝ) : cutCount q Z a ≤ cutCount q W a := by
  unfold cutCount
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hr, ha⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hZW chi hr, ha⟩
  · exact fun _ _ _ => Nat.zero_le _

theorem exceptional_density_budget {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ) (_hd : SourceAt (lowScale N) d e)
    (h14000 : retainedCount q (bulkCap N) (omegaCutoff N q) d e ≤ 14000)
    (h13 : retainedCount q (cap N 0.33) (omegaCutoff N q) d e ≤ 13)
    (hregion : ∀ (chi : Character q) (rho : ℂ), rho ∈ retainedValues chi (omegaCutoff N q) d e →
      rho.re ≤ cap N 0.3221) :
    retainedSum N q (omegaCutoff N q) d e ≤ 8.2e-10 / sourceL N := by
  have h := cutMass_le_three_steps (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (bulkCap N) (cap N 0.33) (cap N 0.3221)
    (cap_positive hN (by norm_num)) (cap_positive hN (by norm_num))
    (fun chi => retainedValues chi (omegaCutoff N q) d e)
    (fun _ => Finset.filter_subset _ _) hregion
  change retainedSum N q (omegaCutoff N q) d e ≤
    bulkSum N q (omegaCutoff N q) (bulkCap N) +
      weight N (cap N 0.33) * retainedCount q (bulkCap N) (omegaCutoff N q) d e +
      weight N (cap N 0.3221) * retainedCount q (cap N 0.33) (omegaCutoff N q) d e at h
  have h1 := mul_le_mul (weight_033_payment hN) (Nat.cast_le.mpr h14000 : (_ : ℝ) ≤ 14000)
    (Nat.cast_nonneg _) (by have := Parameters.sourceL_ge_3100 hN; positivity)
  have h2 := mul_le_mul (weight_03221_payment hN) (Nat.cast_le.mpr h13 : (_ : ℝ) ≤ 13)
    (Nat.cast_nonneg _) (by have := Parameters.sourceL_ge_3100 hN; positivity)
  have hp : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  apply h.trans
  calc
    _ ≤ 6e-10 / sourceL N + (9.486e-15 / sourceL N) * 14000 +
        (2.5296e-14 / sourceL N) * 13 :=
      add_le_add (add_le_add (source_bulk_numeric hN hq) h1) h2
    _ ≤ _ := by
      apply (le_div_iff₀ hp).mpr
      field_simp
      norm_num

theorem nonexceptional_density_budget {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h14000 : familyCount q (bulkCap N) (omegaCutoff N q) ≤ 14000)
    (h13 : familyCount q (cap N 0.33) (omegaCutoff N q) ≤ 13)
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ), rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
      rho.re ≤ cap N (1/9.645908801)) :
    lowSum N q ≤ 0.0194 / sourceL N := by
  let Z := fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q)
  let A := fun chi => (Z chi).filter (fun rho => rho.re ≤ cap N 0.3221)
  let B := fun chi => (Z chi).filter (fun rho => cap N 0.3221 < rho.re)
  have hZA : ∀ chi, A chi ⊆ Z chi := fun _ => Finset.filter_subset _ _
  have hZB : ∀ chi, B chi ⊆ Z chi := fun _ => Finset.filter_subset _ _
  have hcap (c : ℝ) (hc : c ≤ 0.478) : 1/2 ≤ cap N c := by
    have hl : 25 ≤ Real.log (lowScale N) := (log_scale_bounds (Parameters.sourceL_ge_3100 hN)).1
    have hd : c / Real.log (lowScale N) ≤ 1/2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    dsimp [cap]
    linarith
  have hcount (alpha : ℝ) (ha : 1/2 ≤ alpha) :
      cutCount q Z alpha = familyCount q alpha (omegaCutoff N q) := by
    simp only [cutCount, Z, familyCount, count, Applications.values_eq_complete_filter _ ha,
      zeroMultiplicity]
  have hA := cutMass_le_three_steps (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (bulkCap N) (cap N 0.33) (cap N 0.3221)
    (cap_positive hN (by norm_num)) (cap_positive hN (by norm_num))
    A hZA (fun _ _ hr => (Finset.mem_filter.mp hr).2)
  have hcA1 : cutCount q A (bulkCap N) ≤ 14000 := by
    apply (cutCount_mono A Z hZA _).trans
    rw [hcount _ (bulkCap_bounds hN hq).1]
    exact h14000
  have hcA2 : cutCount q A (cap N 0.33) ≤ 13 := by
    apply (cutCount_mono A Z hZA _).trans
    rw [hcount _ (hcap _ (by norm_num))]
    exact h13
  have hcB : cutCount q B (cap N 0.3221) ≤ 2 := by
    apply (cutCount_mono B Z hZB _).trans
    rw [hcount _ (hcap _ (by norm_num))]
    exact h2
  have hB := cutMass_le_count (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (cap N 0.3221) (cap_positive hN (by norm_num : (1/9.645908801 : ℝ) ≤ 0.478))
    B hZB (fun _ _ hr => (Finset.mem_filter.mp hr).2.le)
    (fun chi rho hr => hregion chi rho (hZB chi hr))
  have hp : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hpa := mul_le_mul (weight_033_payment hN) (Nat.cast_le.mpr hcA1 : (_ : ℝ) ≤ 14000)
    (Nat.cast_nonneg _) (by positivity)
  have hpb := mul_le_mul (weight_03221_payment hN) (Nat.cast_le.mpr hcA2 : (_ : ℝ) ≤ 13)
    (Nat.cast_nonneg _) (by positivity)
  have hpc := mul_le_mul (weight_source_c1_payment hN) (Nat.cast_le.mpr hcB : (_ : ℝ) ≤ 2)
    (Nat.cast_nonneg _) (by positivity)
  change cutMass N q Z ≤ _
  rw [cutMass_partition N q Z (cap N 0.3221)]
  apply (add_le_add hA hB).trans
  calc
    _ ≤ (6e-10 / sourceL N + (9.486e-15 / sourceL N) * 14000 +
        (2.5296e-14 / sourceL N) * 13) + (0.00965805 / sourceL N) * 2 :=
      add_le_add (add_le_add (add_le_add (source_bulk_numeric hN hq) hpa) hpb) hpc
    _ ≤ _ := by
      apply (le_div_iff₀ hp).mpr
      field_simp
      norm_num

end LiuWang.Proof.WeightedLowZeros.Continuation
