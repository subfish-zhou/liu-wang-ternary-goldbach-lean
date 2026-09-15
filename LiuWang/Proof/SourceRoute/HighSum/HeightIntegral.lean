import LiuWang.Proof.WeightedHighZeros.Continuation.SourceIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The full height integral in Liu--Wang (2.19)

The count is the actual ordinary-L family count. Zeros below the positive
lower endpoint contribute a nonnegative correction, not a discarded endpoint.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum

def heightKernel (y : ℝ) : ℝ := 1 / y ^ (2 : ℕ)

theorem heightKernel_integrable {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    IntervalIntegrable heightKernel volume u T := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huT]
  exact continuousOn_const.div (continuousOn_id.pow 2)
    (fun y hy => pow_ne_zero _ (ne_of_gt (hu.trans_le hy.1)))

theorem integral_heightKernel {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∫ y in u..T, heightKernel y) = 1 / u - 1 / T := by
  have h := integral_zpow (a := u) (b := T) (n := -2)
    (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt hu (hu.trans_le huT)⟩)
  norm_num [heightKernel, zpow_neg, one_div] at h ⊢
  linarith

theorem height_indicator_integrable {u T : ℝ} (hu : 0 < u) (huT : u ≤ T)
    (t : ℝ) :
    IntervalIntegrable ((Set.Ici t).indicator heightKernel) volume u T := by
  rw [intervalIntegrable_iff]
  exact (heightKernel_integrable hu huT).def'.indicator measurableSet_Ici

theorem integral_height_indicator {u T t : ℝ} (hu : 0 < u)
    (huT : u ≤ T) (htT : t ≤ T) :
    (∫ y in u..T, (Set.Ici t).indicator heightKernel y) =
      1 / max u t - 1 / T := by
  have hmT : max u t ≤ T := max_le huT htT
  have hm : 0 < max u t := hu.trans_le (le_max_left _ _)
  calc
    _ = ∫ y in Set.Icc u T, (Set.Ici t).indicator heightKernel y := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le huT]
    _ = ∫ y in Set.Icc (max u t) T, heightKernel y := by
      rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
      have hs : Set.Ici t ∩ Set.Icc u T = Set.Icc (max u t) T := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, max_le_iff]
        tauto
      rw [hs]
    _ = ∫ y in max u t..T, heightKernel y := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hmT]
    _ = _ := integral_heightKernel hm hmT

theorem zeroValues_height_filter {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y T : ℝ} (hyT : y ≤ T) :
    zeroValues chi alpha y =
      (zeroValues chi alpha T).filter (fun rho => |rho.im| ≤ y) := by
  ext rho
  simp only [Finset.mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨hz, ⟨h0, h1, hy⟩, ha⟩
    exact ⟨⟨hz, ⟨h0, h1, hy.trans hyT⟩, ha⟩, hy⟩
  · rintro ⟨⟨hz, ⟨h0, h1, _⟩, ha⟩, hy⟩
    exact ⟨hz, ⟨h0, h1, hy⟩, ha⟩

theorem count_height_integrand {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y T : ℝ} (hyT : y ≤ T) :
    heightKernel y * (count chi alpha y : ℝ) =
      ∑ rho ∈ zeroValues chi alpha T, (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (Set.Ici |rho.im|).indicator heightKernel y := by
  rw [count, zeroValues_height_filter chi alpha hyT, Nat.cast_sum]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hy : |rho.im| ≤ y <;> simp [Set.mem_Ici, hy, mul_comm]

theorem count_height_integrable {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    IntervalIntegrable (fun y => heightKernel y * (count chi alpha y : ℝ))
      volume u T := by
  have h : IntervalIntegrable
      (fun y => ∑ rho ∈ zeroValues chi alpha T,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Ici |rho.im|).indicator heightKernel y) volume u T := by
    convert! IntervalIntegrable.sum (zeroValues chi alpha T) (fun rho _ =>
      (height_indicator_integrable hu huT |rho.im|).const_mul
        (analyticOrderNatAt chi.LFunction rho : ℝ)) using 1
    ext y
    simp only [Finset.sum_apply]
  apply h.congr
  intro y hy
  rw [Set.uIoc_of_le huT] at hy
  exact (count_height_integrand chi alpha hy.2).symm

theorem integral_count_height {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∫ y in u..T, heightKernel y * (count chi alpha y : ℝ)) =
      ∑ rho ∈ zeroValues chi alpha T,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (1 / max u |rho.im| - 1 / T) := by
  calc
    _ = ∫ y in u..T, ∑ rho ∈ zeroValues chi alpha T,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Ici |rho.im|).indicator heightKernel y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le huT] at hy
      exact count_height_integrand chi alpha hy.2
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro rho hrho
        rw [intervalIntegral.integral_const_mul,
          integral_height_indicator hu huT (mem_zeroValues.mp hrho).2.1.2.2]
      · intro rho _
        exact (height_indicator_integrable hu huT |rho.im|).const_mul _

theorem count_height_identity {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (count chi alpha T : ℝ) / T +
        (∫ y in u..T, heightKernel y * (count chi alpha y : ℝ)) =
      ∑ rho ∈ zeroValues chi alpha T,
        (analyticOrderNatAt chi.LFunction rho : ℝ) / max u |rho.im| := by
  rw [integral_count_height chi alpha hu huT, count, Nat.cast_sum,
    Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem band_reciprocal_le_height_integral {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∑ rho ∈ bandValues chi alpha u T,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤
        (count chi alpha T : ℝ) / T +
          ∫ y in u..T, heightKernel y * (count chi alpha y : ℝ) := by
  rw [count_height_identity chi alpha hu huT]
  calc
    _ = ∑ rho ∈ bandValues chi alpha u T,
        (analyticOrderNatAt chi.LFunction rho : ℝ) / max u |rho.im| := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [max_eq_right (mem_bandValues.mp hrho).2.2.2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun rho _ _ => div_nonneg (Nat.cast_nonneg _)
        (hu.le.trans (le_max_left _ _)))

theorem family_height_integrable (q : ℕ) [NeZero q] (alpha : ℝ)
    {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    IntervalIntegrable (fun y => heightKernel y * (familyCount q alpha y : ℝ))
      volume u T := by
  simp only [familyCount, Nat.cast_sum, Finset.mul_sum]
  convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q)) (fun chi _ =>
    count_height_integrable chi alpha hu huT) using 1
  ext y
  simp only [Finset.sum_apply]

theorem family_reciprocal_le_height_integral (q : ℕ) [NeZero q] (alpha : ℝ)
    {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u T,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤
        (familyCount q alpha T : ℝ) / T +
          ∫ y in u..T, heightKernel y * (familyCount q alpha y : ℝ) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => band_reciprocal_le_height_integral chi alpha hu huT)
  simpa only [Finset.sum_add_distrib, familyCount, Nat.cast_sum, Finset.sum_div,
    Finset.mul_sum, intervalIntegral.integral_finsetSum
      (fun chi _ => count_height_integrable chi alpha hu huT)] using h

end LiuWang.Proof.SourceRoute.HighSum
