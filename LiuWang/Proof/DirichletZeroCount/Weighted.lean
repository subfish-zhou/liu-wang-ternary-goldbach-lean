import LiuWang.Proof.DirichletZeroCount.HighHeight

/-!
# Actual finite zero sums on closed bands bounded away from zero

The lower cutoff is positive in the reciprocal consumers, so a possible
nonprincipal real zero is never silently discarded by totalized inversion.
Both band endpoints are included. Adjacent bands can overcount their common
endpoint; no disjoint partition identity is asserted.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount

def bandValues {q : ℕ} [NeZero q] (chi : Character q) (alpha u y : ℝ) : Finset ℂ :=
  (zeroValues chi alpha y).filter (fun rho => u ≤ |rho.im|)

theorem mem_bandValues {q : ℕ} [NeZero q] {chi : Character q}
    {alpha u y : ℝ} {rho : ℂ} :
    rho ∈ bandValues chi alpha u y ↔
      chi.LFunction rho = 0 ∧ (0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ y) ∧
        alpha ≤ rho.re ∧ u ≤ |rho.im| := by
  simp only [bandValues, Finset.mem_filter, mem_zeroValues]
  tauto

theorem band_weighted_sum_le_count {q : ℕ} [NeZero q] (chi : Character q)
    (alpha u y : ℝ) (f : ℂ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ rho ∈ bandValues chi alpha u y, f rho ≤ M) :
    (∑ rho ∈ bandValues chi alpha u y, (analyticOrderNatAt chi.LFunction rho : ℝ) * f rho) ≤
      M * count chi alpha y := by
  calc
    _ ≤ ∑ rho ∈ bandValues chi alpha u y, (analyticOrderNatAt chi.LFunction rho : ℝ) * M := by
      exact Finset.sum_le_sum (fun rho hrho =>
        mul_le_mul_of_nonneg_left (hf rho hrho) (Nat.cast_nonneg _))
    _ ≤ ∑ rho ∈ zeroValues chi alpha y, (analyticOrderNatAt chi.LFunction rho : ℝ) * M :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) hM)
    _ = _ := by simp [count, Nat.cast_sum, Finset.mul_sum, mul_comm]

theorem band_weighted_sum_le {q : ℕ} [NeZero q] (chi : Character q)
    (alpha u : ℝ) {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a)
    (f : ℂ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ rho ∈ bandValues chi alpha u y, f rho ≤ M) :
    (∑ rho ∈ bandValues chi alpha u y, (analyticOrderNatAt chi.LFunction rho : ℝ) * f rho) ≤
      M * sharpenedBound chi y a :=
  (band_weighted_sum_le_count chi alpha u y f hM hf).trans
    (mul_le_mul_of_nonneg_left (count_le_sharpenedBound chi alpha hy ha) hM)

theorem band_inverse_sum_le {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤ sharpenedBound chi y a / u := by
  have hf (rho : ℂ) (hrho : rho ∈ bandValues chi alpha u y) :
      1 / |rho.im| ≤ 1 / u :=
    one_div_le_one_div_of_le hu (mem_bandValues.mp hrho).2.2.2
  simpa only [mul_one_div, one_div_mul_eq_div] using
    band_weighted_sum_le chi alpha u hy ha (fun rho => 1 / |rho.im|) (by positivity) hf

theorem band_inverse_sqrt_sum_le {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
        sharpenedBound chi y a / Real.sqrt u := by
  have hf (rho : ℂ) (hrho : rho ∈ bandValues chi alpha u y) :
      1 / Real.sqrt |rho.im| ≤ 1 / Real.sqrt u :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hu)
      (Real.sqrt_le_sqrt (mem_bandValues.mp hrho).2.2.2)
  simpa only [mul_one_div, one_div_mul_eq_div] using
    band_weighted_sum_le chi alpha u hy ha (fun rho => 1 / Real.sqrt |rho.im|) (by positivity) hf

theorem normalized_family_inverse_sum_le (q : ℕ) [NeZero q] (alpha : ℝ)
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) / q.totient ≤
        (∑ chi : Character q, sharpenedBound chi y a) / (u * q.totient) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => band_inverse_sum_le chi alpha hu hy ha)
  rw [← Finset.sum_div] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by ring)

theorem normalized_family_inverse_sqrt_sum_le (q : ℕ) [NeZero q] (alpha : ℝ)
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) / q.totient ≤
        (∑ chi : Character q, sharpenedBound chi y a) / (Real.sqrt u * q.totient) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => band_inverse_sqrt_sum_le chi alpha hu hy ha)
  rw [← Finset.sum_div] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by ring)

end LiuWang.Proof.DirichletZeroCount
