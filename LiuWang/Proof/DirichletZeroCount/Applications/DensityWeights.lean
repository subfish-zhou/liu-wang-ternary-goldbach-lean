import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

/-! # Low-alpha density payments on the complete-S closed weighted bands -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount.Applications

theorem family_band_weighted_sum_le_count (q : ℕ) [NeZero q] (alpha u y : ℝ)
    (f : Character q → ℂ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ chi rho, rho ∈ bandValues chi alpha u y → f chi rho ≤ M) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * f chi rho) ≤ M * familyCount q alpha y := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => band_weighted_sum_le_count chi alpha u y (f chi) hM (hf chi))
  simpa only [familyCount, Nat.cast_sum, Finset.mul_sum] using h

theorem family_band_weighted_sum_le_ten (q : ℕ) [NeZero q] (alpha u : ℝ)
    {y : ℝ} (hy : 10000 ≤ y) (f : Character q → ℂ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ chi rho, rho ∈ bandValues chi alpha u y → f chi rho ≤ M) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * f chi rho) ≤
        M * (10 * q * y * Real.log ((q : ℝ) * y)) :=
  (family_band_weighted_sum_le_count q alpha u y f hM hf).trans
    (mul_le_mul_of_nonneg_left (familyCount_le_ten q alpha hy) hM)

theorem family_band_weighted_sum_le_sourceSeven_low (q : ℕ) [NeZero q]
    {alpha u y : ℝ} (hy : 10000 ≤ y) (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 2 / 3)
    (f : Character q → ℂ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ chi rho, rho ∈ bandValues chi alpha u y → f chi rho ≤ M) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * f chi rho) ≤
        M * sourceSevenBound q alpha y :=
  (family_band_weighted_sum_le_count q alpha u y f hM hf).trans
    (mul_le_mul_of_nonneg_left (familyCount_le_sourceSeven_low q hy halpha halpha') hM)

theorem band_values_eq_complete_filter {q : ℕ} [NeZero q] (chi : Character q)
    {alpha : ℝ} (halpha : 1 / 2 ≤ alpha) (u y : ℝ) :
    bandValues chi alpha u y =
      (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re ∧ u ≤ |rho.im|) := by
  simp only [bandValues, values_eq_complete_filter _ halpha, Finset.filter_filter]

theorem normalized_complete_inverse_sourceSeven_low (q : ℕ) [NeZero q]
    {alpha u y : ℝ} (hu : 0 < u) (hy : 10000 ≤ y)
    (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 2 / 3) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter
        (fun rho => alpha ≤ rho.re ∧ u ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) / q.totient ≤
            sourceSevenBound q alpha y / (u * q.totient) := by
  have hf (chi : Character q) (rho : ℂ) (hrho : rho ∈ bandValues chi alpha u y) :
      1 / |rho.im| ≤ 1 / u :=
    one_div_le_one_div_of_le hu (mem_bandValues.mp hrho).2.2.2
  have h := family_band_weighted_sum_le_sourceSeven_low q hy halpha halpha'
    (fun _ rho => 1 / |rho.im|) (by positivity) hf
  simp only [band_values_eq_complete_filter _ halpha, mul_one_div, one_div_mul_eq_div] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by ring)

theorem normalized_complete_inverse_sqrt_sourceSeven_low (q : ℕ) [NeZero q]
    {alpha u y : ℝ} (hu : 0 < u) (hy : 10000 ≤ y)
    (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 2 / 3) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter
        (fun rho => alpha ≤ rho.re ∧ u ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) / q.totient ≤
            sourceSevenBound q alpha y / (Real.sqrt u * q.totient) := by
  have hf (chi : Character q) (rho : ℂ) (hrho : rho ∈ bandValues chi alpha u y) :
      1 / Real.sqrt |rho.im| ≤ 1 / Real.sqrt u :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hu)
      (Real.sqrt_le_sqrt (mem_bandValues.mp hrho).2.2.2)
  have h := family_band_weighted_sum_le_sourceSeven_low q hy halpha halpha'
    (fun _ rho => 1 / Real.sqrt |rho.im|) (by positivity) hf
  simp only [band_values_eq_complete_filter _ halpha, mul_one_div, one_div_mul_eq_div] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by ring)

theorem normalized_complete_inverse_sourceSeven_original_low (q : ℕ) [NeZero q]
    {alpha u y : ℝ} (hu : 0 < u)
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 1 / 2 + 2 * sourceDelta y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter
        (fun rho => alpha ≤ rho.re ∧ u ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) / q.totient ≤
            sourceSevenBound q alpha y / (u * q.totient) := by
  have hy' := source_height_ge_ten_thousand hy
  exact normalized_complete_inverse_sourceSeven_low q hu hy' halpha
    (by linarith [sourceDelta_le_twelfth hy'])

theorem normalized_complete_inverse_sqrt_sourceSeven_original_low (q : ℕ) [NeZero q]
    {alpha u y : ℝ} (hu : 0 < u)
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 1 / 2 + 2 * sourceDelta y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter
        (fun rho => alpha ≤ rho.re ∧ u ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) / q.totient ≤
            sourceSevenBound q alpha y / (Real.sqrt u * q.totient) := by
  have hy' := source_height_ge_ten_thousand hy
  exact normalized_complete_inverse_sqrt_sourceSeven_low q hu hy' halpha
    (by linarith [sourceDelta_le_twelfth hy'])

end LiuWang.Proof.DirichletZeroCount.Applications
