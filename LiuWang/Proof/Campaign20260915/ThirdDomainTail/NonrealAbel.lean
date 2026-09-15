import LiuWang.Proof.SourceRoute.ThirdArc.DensityIntegrals

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.ThirdArc

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem real_zero_filter {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (zeroValues chi alpha y).filter (fun rho => rho.im = 0) =
      zeroValues chi alpha 0 := by
  ext rho
  simp only [Finset.mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨⟨hz, ⟨h0, h1, _⟩, ha⟩, hr⟩
    exact ⟨hz, ⟨h0, h1, by simp [hr]⟩, ha⟩
  · rintro ⟨hz, ⟨h0, h1, hh⟩, ha⟩
    have hr : rho.im = 0 := abs_nonpos_iff.mp hh
    exact ⟨⟨hz, ⟨h0, h1, hh.trans hy⟩, ha⟩, hr⟩

theorem count_sub_real_eq_sum_nonreal {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) - (count chi alpha 0 : ℝ) =
      ∑ rho ∈ (zeroValues chi alpha y).filter (fun rho => rho.im ≠ 0),
        (analyticOrderNatAt chi.LFunction rho : ℝ) := by
  have h := Finset.sum_filter_add_sum_filter_not (zeroValues chi alpha y)
    (fun rho => rho.im = 0) (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ))
  rw [real_zero_filter chi alpha hy] at h
  simp only [count, Nat.cast_sum]
  linarith only [h]

theorem band_cumulative_le_count_sub_real {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u y v : ℝ} (hu : 0 < u) (hy : 0 ≤ y) :
    cumulative (bandValues chi alpha u v) (fun rho => |rho.im|)
        (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ)) y ≤
      (count chi alpha y : ℝ) - (count chi alpha 0 : ℝ) := by
  rw [count_sub_real_eq_sum_nonreal chi alpha hy]
  unfold cumulative
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hr, hh⟩ := Finset.mem_filter.mp hr
    obtain ⟨hz, ⟨h0, h1, _⟩, ha, hl⟩ := mem_bandValues.mp hr
    exact Finset.mem_filter.mpr
      ⟨mem_zeroValues.mpr ⟨hz, ⟨h0, h1, hh⟩, ha⟩,
        abs_pos.mp (hu.trans_le hl)⟩
  · intro rho _ _
    exact Nat.cast_nonneg _

theorem count_sub_real_height_integrable {q : ℕ} [NeZero q] (chi : Character q)
    (alpha p : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable
      (fun y => heightKernel p y * ((count chi alpha y : ℝ) - (count chi alpha 0 : ℝ)))
      volume u v := by
  simpa only [mul_sub] using
    (count_height_integrable chi alpha p hu huv).sub
      ((heightKernel_integrable hu huv p).mul_const (count chi alpha 0 : ℝ))

theorem character_height_partialSummation_sub_real {q : ℕ} [NeZero q]
    (chi : Character q) (alpha : ℝ) {u v p : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    (∑ rho ∈ bandValues chi alpha u v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)) ≤
      v ^ (-p) * ((count chi alpha v : ℝ) - (count chi alpha 0 : ℝ)) +
        ∫ y in u..v,
          heightKernel p y * ((count chi alpha y : ℝ) - (count chi alpha 0 : ℝ)) := by
  have h := finite_height_partialSummation (bandValues chi alpha u v)
    (fun rho => |rho.im|) (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ))
    hu huv hp (fun _ _ => Nat.cast_nonneg _) (by
      intro rho hr
      exact ⟨(mem_bandValues.mp hr).2.2.2, (mem_bandValues.mp hr).2.1.2.2⟩)
  apply h.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hu.trans_le huv).le _)
    rw [count_sub_real_eq_sum_nonreal chi alpha (hu.trans_le huv).le]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hr
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hr).1, abs_pos.mp (hu.trans_le (mem_bandValues.mp hr).2.2.2)⟩
    · intro rho _ _
      exact Nat.cast_nonneg _
  · apply intervalIntegral.integral_mono_on huv
      (cumulative_integrable _ _ _ (heightKernel_integrable hu huv p))
      (count_sub_real_height_integrable chi alpha p hu huv)
    intro y hy
    exact mul_le_mul_of_nonneg_left
      (band_cumulative_le_count_sub_real chi alpha hu (hu.trans_le hy.1).le)
      (mul_nonneg hp (Real.rpow_nonneg (hu.trans_le hy.1).le _))

theorem family_sub_real_height_integrable (q : ℕ) [NeZero q] (alpha p : ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable
      (fun y => heightKernel p y * ((familyCount q alpha y : ℝ) -
        (familyCount q alpha 0 : ℝ))) volume u v := by
  simpa only [mul_sub] using
    (family_height_integrable q alpha p hu huv).sub
      ((heightKernel_integrable hu huv p).mul_const (familyCount q alpha 0 : ℝ))

theorem family_height_partialSummation_sub_real (q : ℕ) [NeZero q] (alpha : ℝ)
    {u v p : ℝ} (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    densityBand q alpha u v p ≤
      v ^ (-p) * ((familyCount q alpha v : ℝ) - (familyCount q alpha 0 : ℝ)) +
        ∫ y in u..v,
          heightKernel p y * ((familyCount q alpha y : ℝ) - (familyCount q alpha 0 : ℝ)) := by
  calc
    _ ≤ ∑ chi : Character q,
        (v ^ (-p) * ((count chi alpha v : ℝ) - (count chi alpha 0 : ℝ)) +
          ∫ y in u..v, heightKernel p y *
            ((count chi alpha y : ℝ) - (count chi alpha 0 : ℝ))) :=
      Finset.sum_le_sum (fun chi _ =>
        character_height_partialSummation_sub_real chi alpha hu huv hp)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← intervalIntegral.integral_finsetSum
          (fun chi _ => count_sub_real_height_integrable chi alpha p hu huv)]
      simp only [familyCount, Nat.cast_sum, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]

theorem family_height_partialSummation_real_credit (q : ℕ) [NeZero q] (alpha : ℝ)
    {u v p : ℝ} (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    densityBand q alpha u v p + u ^ (-p) * (familyCount q alpha 0 : ℝ) ≤
      v ^ (-p) * (familyCount q alpha v : ℝ) +
        ∫ y in u..v, heightKernel p y * (familyCount q alpha y : ℝ) := by
  have h := family_height_partialSummation_sub_real q alpha hu huv hp
  simp_rw [mul_sub] at h
  rw [intervalIntegral.integral_sub (family_height_integrable q alpha p hu huv)
    ((heightKernel_integrable hu huv p).mul_const (familyCount q alpha 0 : ℝ)),
    intervalIntegral.integral_mul_const, integral_heightKernel hu huv p] at h
  nlinarith only [h]

#print axioms count_sub_real_eq_sum_nonreal
#print axioms family_height_partialSummation_sub_real
#print axioms family_height_partialSummation_real_credit

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
