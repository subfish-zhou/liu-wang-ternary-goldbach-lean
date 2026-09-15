import LiuWang.Proof.SourceRoute.ThirdArc.PartialSummation
import LiuWang.Proof.DirichletZeroCount.Weighted

/-! Equations (5.29) and (5.39) with the actual full-character counting function. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc

theorem zeroValues_height_filter {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y v : ℝ} (hy : y ≤ v) :
    zeroValues chi alpha y =
      (zeroValues chi alpha v).filter (fun rho => |rho.im| ≤ y) := by
  ext rho
  simp only [Finset.mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨hz, ⟨h0, h1, hh⟩, ha⟩
    exact ⟨⟨hz, ⟨h0, h1, hh.trans hy⟩, ha⟩, hh⟩
  · tauto

theorem count_eq_cumulative {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y v : ℝ} (hy : y ≤ v) :
    (count chi alpha y : ℝ) =
      cumulative (zeroValues chi alpha v) (fun rho => |rho.im|)
        (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ)) y := by
  simp only [count, zeroValues_height_filter chi alpha hy, Nat.cast_sum, cumulative]

theorem count_height_integrable {q : ℕ} [NeZero q] (chi : Character q)
    (alpha p : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun y => heightKernel p y * count chi alpha y) volume u v := by
  apply (cumulative_integrable (zeroValues chi alpha v) (fun rho => |rho.im|)
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ))
    (heightKernel_integrable hu huv p)).congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huv] at hy
  dsimp only
  rw [count_eq_cumulative chi alpha hy.2]

theorem band_cumulative_le_count {q : ℕ} [NeZero q] (chi : Character q)
    (alpha u : ℝ) {y v : ℝ} (hy : y ≤ v) :
    cumulative (bandValues chi alpha u v) (fun rho => |rho.im|)
        (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ)) y ≤
      count chi alpha y := by
  rw [count_eq_cumulative chi alpha hy]
  unfold cumulative
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    obtain ⟨hrho, hh⟩ := Finset.mem_filter.mp hrho
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hrho).1, hh⟩
  · intro rho _ _
    exact Nat.cast_nonneg _

theorem character_height_partialSummation {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {u v p : ℝ} (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    (∑ rho ∈ bandValues chi alpha u v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)) ≤
      v ^ (-p) * count chi alpha v +
        ∫ y in u..v, heightKernel p y * count chi alpha y := by
  have h := finite_height_partialSummation (bandValues chi alpha u v)
    (fun rho => |rho.im|) (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ))
    hu huv hp (fun _ _ => Nat.cast_nonneg _) (by
      intro rho hrho
      have hr := mem_bandValues.mp hrho
      exact ⟨hr.2.2.2, hr.2.1.2.2⟩)
  apply h.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hu.trans_le huv).le _)
    simp only [count, Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.cast_nonneg _)
  · apply intervalIntegral.integral_mono_on huv
      (cumulative_integrable _ _ _ (heightKernel_integrable hu huv p))
      (count_height_integrable chi alpha p hu huv)
    intro y hy
    exact mul_le_mul_of_nonneg_left (band_cumulative_le_count chi alpha u hy.2)
      (mul_nonneg hp (Real.rpow_nonneg (hu.trans_le hy.1).le _))

def densityBand (q : ℕ) [NeZero q] (alpha u v p : ℝ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u v,
    (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)

theorem family_height_integrable (q : ℕ) [NeZero q] (alpha p : ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun y => heightKernel p y * familyCount q alpha y) volume u v := by
  simp only [familyCount, Nat.cast_sum, Finset.mul_sum]
  convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
    (fun chi _ => count_height_integrable chi alpha p hu huv) using 1
  ext y
  simp only [Finset.sum_apply]

theorem family_height_partialSummation (q : ℕ) [NeZero q] (alpha : ℝ)
    {u v p : ℝ} (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    densityBand q alpha u v p ≤ v ^ (-p) * familyCount q alpha v +
      ∫ y in u..v, heightKernel p y * familyCount q alpha y := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => character_height_partialSummation chi alpha hu huv hp)
  simp only [densityBand, familyCount, Nat.cast_sum, Finset.mul_sum,
    Finset.sum_add_distrib] at h ⊢
  rw [intervalIntegral.integral_finsetSum (fun chi _ =>
    count_height_integrable chi alpha p hu huv)]
  exact h

theorem equation_5_29 (q : ℕ) [NeZero q] (alpha : ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
      (1 / Real.sqrt v) * familyCount q alpha v +
        (1 / 2 : ℝ) * ∫ y in u..v, y ^ (-3 / 2 : ℝ) * familyCount q alpha y := by
  have h := family_height_partialSummation q alpha hu huv (p := 1 / 2) (by norm_num)
  simp only [densityBand, heightKernel,
    show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    Real.rpow_neg (abs_nonneg _), Real.rpow_neg (hu.trans_le huv).le,
    ← Real.sqrt_eq_rpow, mul_assoc, intervalIntegral.integral_const_mul] at h
  simpa only [div_eq_mul_inv, one_mul] using h

theorem equation_5_39 (q : ℕ) [NeZero q] (alpha : ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤
      (1 / v) * familyCount q alpha v +
        ∫ y in u..v, y ^ (-2 : ℝ) * familyCount q alpha y := by
  have h := family_height_partialSummation q alpha hu huv (p := 1) (by norm_num)
  simpa only [densityBand, heightKernel, Real.rpow_neg_one, one_mul, one_div,
    div_eq_mul_inv, show -(1 : ℝ) - 1 = -2 by norm_num] using h

end LiuWang.Proof.SourceRoute.ThirdArc
