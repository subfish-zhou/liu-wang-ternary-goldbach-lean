import LiuWang.Proof.DirichletZeroCount.Remainder.UniformFamily
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

/-! # Sharpened original-height counts paying the actual complete-S weighted zero bands -/

set_option autoImplicit false
noncomputable section
open scoped Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem family_band_weighted_le_uniform (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) (u : ℝ) (f : Character q → ℂ → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ chi rho, rho ∈ bandValues chi alpha u y → f chi rho ≤ M) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * f chi rho) ≤ M * uniformFamilyBound q y := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => band_weighted_sum_le_count chi alpha u y (f chi) hM (hf chi))
  rw [← Finset.mul_sum] at hh
  have he : (∑ chi : Character q, (count chi alpha y : ℝ)) = (familyCount q alpha y : ℝ) := by
    simp only [familyCount, Nat.cast_sum]
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (familyCount_le_uniformFamilyBound q ha hy) hM)

theorem normalized_family_inverse_le_uniform (q : ℕ) [NeZero q] {alpha u y : ℝ}
    (ha : 0 ≤ alpha) (hu : 0 < u) (hy : 0 ≤ y) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) / q.totient ≤
        uniformFamilyBound q y / (u * q.totient) := by
  have hh := family_band_weighted_le_uniform q ha hy u
    (fun _ rho => 1 / |rho.im|) (M := 1 / u) (by positivity)
    (fun _ _ hr => one_div_le_one_div_of_le hu (mem_bandValues.mp hr).2.2.2)
  simp only [mul_one_div, one_div_mul_eq_div] at hh
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)).trans_eq (by ring)

theorem normalized_family_inverse_sqrt_le_uniform (q : ℕ) [NeZero q] {alpha u y : ℝ}
    (ha : 0 ≤ alpha) (hu : 0 < u) (hy : 0 ≤ y) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u y,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) / q.totient ≤
        uniformFamilyBound q y / (Real.sqrt u * q.totient) := by
  have hh := family_band_weighted_le_uniform q ha hy u
    (fun _ rho => 1 / Real.sqrt |rho.im|) (M := 1 / Real.sqrt u) (by positivity)
    (fun _ _ hr => one_div_le_one_div_of_le (Real.sqrt_pos.mpr hu)
      (Real.sqrt_le_sqrt (mem_bandValues.mp hr).2.2.2))
  simp only [mul_one_div, one_div_mul_eq_div] at hh
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)).trans_eq (by ring)

theorem complete_family_le_uniform (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    (∑ chi : Character q, ∑ rho ∈ CompleteExpansion.zeroValues chi y,
      (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ uniformFamilyBound q y := by
  simpa only [Applications.familyCount_half_eq_complete, Nat.cast_sum] using
    familyCount_le_uniformFamilyBound q (alpha := 1 / 2) (by norm_num) hy

theorem normalized_complete_inverse_le_uniform (q : ℕ) [NeZero q]
    {u y : ℝ} (hu : 0 < u) (hy : 0 ≤ y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) / q.totient ≤
          uniformFamilyBound q y / (u * q.totient) := by
  simpa only [bandValues, Applications.half_values_eq_complete] using
    normalized_family_inverse_le_uniform q (alpha := 1 / 2) (by norm_num) hu hy

theorem normalized_complete_inverse_sqrt_le_uniform (q : ℕ) [NeZero q]
    {u y : ℝ} (hu : 0 < u) (hy : 0 ≤ y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) / q.totient ≤
          uniformFamilyBound q y / (Real.sqrt u * q.totient) := by
  simpa only [bandValues, Applications.half_values_eq_complete] using
    normalized_family_inverse_sqrt_le_uniform q (alpha := 1 / 2) (by norm_num) hu hy

end LiuWang.Proof.DirichletZeroCount.Remainder
