import LiuWang.Proof.SourceRoute.HighSum.SourceReduction

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.WeightedHighZeros.Continuation
open LiuWang.Proof.SourceRoute.HighSum

namespace LiuWang.Proof.Campaign20260915.HighSums

def belowHeightCount {q : ℕ} [NeZero q] (chi : Character q) (alpha u : ℝ) : ℕ :=
  ∑ rho ∈ (zeroValues chi alpha u).filter (fun rho => |rho.im| < u),
    analyticOrderNatAt chi.LFunction rho

def belowHeightFamilyCount (q : ℕ) [NeZero q] (alpha u : ℝ) : ℕ :=
  ∑ chi : Character q, belowHeightCount chi alpha u

theorem below_height_filter {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u T : ℝ} (huT : u ≤ T) :
    (zeroValues chi alpha T).filter (fun rho => |rho.im| < u) =
      (zeroValues chi alpha u).filter (fun rho => |rho.im| < u) := by
  ext rho
  simp only [Finset.mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨⟨hz, ⟨h0, h1, _⟩, ha⟩, hu⟩
    exact ⟨⟨hz, ⟨h0, h1, hu.le⟩, ha⟩, hu⟩
  · rintro ⟨⟨hz, ⟨h0, h1, _⟩, ha⟩, hu⟩
    exact ⟨⟨hz, ⟨h0, h1, hu.le.trans huT⟩, ha⟩, hu⟩

/-- The lower boundary belongs to the high band, not to its compensation. -/
theorem band_reciprocal_add_below_height {q : ℕ} [NeZero q]
    (chi : Character q) (alpha : ℝ) {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∑ rho ∈ bandValues chi alpha u T,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) +
        (belowHeightCount chi alpha u : ℝ) / u =
      (count chi alpha T : ℝ) / T +
        ∫ y in u..T, heightKernel y * (count chi alpha y : ℝ) := by
  rw [count_height_identity chi alpha hu huT]
  unfold belowHeightCount
  rw [← below_height_filter chi alpha huT]
  simp only [bandValues, Nat.cast_sum, Finset.sum_div, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hr : u ≤ |rho.im|
  · simp [hr, not_lt.mpr hr]
  · have hr' : |rho.im| < u := lt_of_not_ge hr
    simp [hr, hr', max_eq_left hr'.le]

theorem family_reciprocal_add_below_height (q : ℕ) [NeZero q]
    (alpha : ℝ) {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u T,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) +
        (belowHeightFamilyCount q alpha u : ℝ) / u =
      (familyCount q alpha T : ℝ) / T +
        ∫ y in u..T, heightKernel y * (familyCount q alpha y : ℝ) := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Character q))) rfl
    (fun chi _ => band_reciprocal_add_below_height chi alpha hu huT)
  simpa only [Finset.sum_add_distrib, belowHeightFamilyCount, familyCount,
    Nat.cast_sum, Finset.sum_div, Finset.mul_sum,
    intervalIntegral.integral_finsetSum
      (fun chi _ => count_height_integrable chi alpha hu huT)] using h

theorem sourceMass_eq_compensated_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (alpha : ℝ) :
    sourceMass N q alpha =
      (familyCount q alpha (sourceT N) : ℝ) / sourceT N +
        (∫ y in omegaCutoff N q..sourceT N,
          heightKernel y * (familyCount q alpha y : ℝ)) -
        (belowHeightFamilyCount q alpha (omegaCutoff N q) : ℝ) / omegaCutoff N q := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have h := family_reciprocal_add_below_height q alpha hu
    (WeightedLowZeros.omegaCutoff_le_sourceT hN)
  change sourceMass N q alpha + _ = _ at h
  linarith

theorem below_height_correction_nonneg (q : ℕ) [NeZero q]
    (alpha : ℝ) {u : ℝ} (hu : 0 < u) :
    0 ≤ (belowHeightFamilyCount q alpha u : ℝ) / u :=
  div_nonneg (Nat.cast_nonneg _) hu.le

#print axioms band_reciprocal_add_below_height
#print axioms family_reciprocal_add_below_height
#print axioms sourceMass_eq_compensated_height

end LiuWang.Proof.Campaign20260915.HighSums
