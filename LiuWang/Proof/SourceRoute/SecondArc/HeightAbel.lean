import LiuWang.Proof.SourceRoute.SecondArc.FiniteAbel
import LiuWang.Proof.DirichletZeroCount.Applications.DensityWeights

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc

theorem count_eq_cumulative {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y v : ℝ} (hyv : y ≤ v) :
    (count chi alpha y : ℝ) =
      cumulativeWeight (zeroValues chi alpha v) (fun rho => |rho.im|)
        (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ)) y := by
  have he : (zeroValues chi alpha v).filter (fun rho => |rho.im| ≤ y) =
      zeroValues chi alpha y := by
    ext rho
    simp only [Finset.mem_filter, mem_zeroValues]
    constructor
    · rintro ⟨⟨hz, ⟨h0, h1, _⟩, ha⟩, hh⟩
      exact ⟨hz, ⟨h0, h1, hh⟩, ha⟩
    · rintro ⟨hz, ⟨h0, h1, hh⟩, ha⟩
      exact ⟨⟨hz, ⟨h0, h1, hh.trans hyv⟩, ha⟩, hh⟩
  simp only [cumulativeWeight, he, count, Nat.cast_sum]

theorem count_height_integrable {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun y => heightKernel y * (count chi alpha y : ℝ))
      volume u v := by
  apply (height_integrand_integrable (zeroValues chi alpha v)
    (fun rho => |rho.im|) (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ))
    hu huv).congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huv] at hy
  dsimp only
  rw [count_eq_cumulative chi alpha hy.2]

theorem familyCount_height_integrable (q : ℕ) [NeZero q] (alpha : ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun y => heightKernel y * (familyCount q alpha y : ℝ))
      volume u v := by
  simp only [familyCount, Nat.cast_sum, Finset.mul_sum]
  convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
    (fun chi _ => count_height_integrable chi alpha hu huv) using 1
  ext y
  simp only [Finset.sum_apply]

theorem character_height_abel {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∑ rho ∈ bandValues chi alpha u v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
      (count chi alpha v : ℝ) / Real.sqrt v +
        (1 / 2 : ℝ) * ∫ y in u..v, heightKernel y * (count chi alpha y : ℝ) := by
  have h := finite_height_abel_le (s := bandValues chi alpha u v)
    (t := zeroValues chi alpha v) (fun rho => |rho.im|)
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ)) hu huv
    (Finset.filter_subset _ _) (fun _ _ => Nat.cast_nonneg _)
    (fun rho hr => ⟨(mem_bandValues.mp hr).2.2.2, (mem_bandValues.mp hr).2.1.2.2⟩)
  have he :
      (∫ y in u..v, heightKernel y *
        cumulativeWeight (zeroValues chi alpha v) (fun rho => |rho.im|)
          (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ)) y) =
        ∫ y in u..v, heightKernel y * (count chi alpha y : ℝ) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le huv] at hy
    dsimp only
    rw [count_eq_cumulative chi alpha hy.2]
  rw [he] at h
  simpa only [count, Nat.cast_sum] using h

/-- Equation (5.4), on the actual closed ordinary-L zero sets. -/
theorem family_height_abel (q : ℕ) [NeZero q] (alpha : ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
      (familyCount q alpha v : ℝ) / Real.sqrt v +
        (1 / 2 : ℝ) * ∫ y in u..v, heightKernel y * (familyCount q alpha y : ℝ) := by
  calc
    _ ≤ ∑ chi : Character q, ((count chi alpha v : ℝ) / Real.sqrt v +
        (1 / 2 : ℝ) * ∫ y in u..v, heightKernel y * (count chi alpha y : ℝ)) :=
      Finset.sum_le_sum (fun chi _ => character_height_abel chi alpha hu huv)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div,
        familyCount, Nat.cast_sum, Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum
        (fun chi _ => count_height_integrable chi alpha hu huv)]
      rw [Finset.mul_sum]

theorem normalized_complete_height_abel (q : ℕ) [NeZero q] {alpha : ℝ}
    (ha : 1 / 2 ≤ alpha) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (Real.sqrt q / q.totient) *
      (∑ chi : Character q,
        ∑ rho ∈ (LiuWang.Proof.CompleteExpansion.zeroValues chi v).filter
          (fun rho => alpha ≤ rho.re ∧ u ≤ |rho.im|),
            (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
      (Real.sqrt q / q.totient) *
        ((familyCount q alpha v : ℝ) / Real.sqrt v +
          (1 / 2 : ℝ) * ∫ y in u..v, heightKernel y * (familyCount q alpha y : ℝ)) := by
  simp_rw [← Applications.band_values_eq_complete_filter _ ha]
  exact mul_le_mul_of_nonneg_left (family_height_abel q alpha hu huv) (by positivity)

end LiuWang.Proof.SourceRoute.SecondArc
