import LiuWang.Proof.SourceRoute.SecondArc.AlphaIntegral
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc

theorem count_alpha_integrable {q : ℕ} [NeZero q] {x a b : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (y : ℝ) :
    IntervalIntegrable (fun alpha => alphaKernel x alpha * (familyCount q alpha y : ℝ))
      volume a b := by
  have he (alpha : ℝ) (ha : a ≤ alpha) :
      alphaKernel x alpha * (familyCount q alpha y : ℝ) =
        ∑ chi : Character q, ∑ rho ∈ zeroValues chi a y,
          (analyticOrderNatAt chi.LFunction rho : ℝ) *
            (Set.Iic rho.re).indicator (alphaKernel x) alpha := by
    have hs (chi : Character q) : zeroValues chi alpha y =
        (zeroValues chi a y).filter (fun rho => alpha ≤ rho.re) := by
      ext rho
      simp only [mem_zeroValues, Finset.mem_filter]
      constructor
      · rintro ⟨hz, hs, hb⟩
        exact ⟨⟨hz, hs, ha.trans hb⟩, hb⟩
      · rintro ⟨⟨hz, hs, _⟩, hb⟩
        exact ⟨hz, hs, hb⟩
    simp only [familyCount, count, hs, Nat.cast_sum, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi _
    apply Finset.sum_congr rfl
    intro rho _
    by_cases hb : alpha ≤ rho.re <;> simp [Set.indicator, hb, mul_comm]
  have hc (chi : Character q) : IntervalIntegrable (fun alpha =>
      ∑ rho ∈ zeroValues chi a y, (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (Set.Iic rho.re).indicator (alphaKernel x) alpha) volume a b := by
    convert! IntervalIntegrable.sum (zeroValues chi a y) (fun rho _ =>
      (alpha_indicator_integrable hx a b rho.re).const_mul
        (analyticOrderNatAt chi.LFunction rho : ℝ)) using 1
    ext alpha
    simp only [Finset.sum_apply]
  have hi : IntervalIntegrable (fun alpha => ∑ chi : Character q,
      ∑ rho ∈ zeroValues chi a y, (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (Set.Iic rho.re).indicator (alphaKernel x) alpha) volume a b := by
    convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
      (fun chi _ => hc chi) using 1
    ext alpha
    simp only [Finset.sum_apply]
  apply hi.congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro alpha halpha
  rw [Set.uIoc_of_le hab] at halpha
  exact (he alpha halpha.1.le).symm

theorem density_rectangle_finite {q : ℕ} [NeZero q] {a alpha y v : ℝ}
    (ha : a ≤ alpha) (hy : y ≤ v) (x : ℝ) :
    alphaKernel x alpha * heightKernel y * (familyCount q alpha y : ℝ) =
      ∑ chi : Character q, ∑ rho ∈ zeroValues chi a v,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Iic rho.re).indicator (alphaKernel x) alpha) *
            (Set.Ici |rho.im|).indicator heightKernel y := by
  have hs (chi : Character q) : zeroValues chi alpha y =
      (zeroValues chi a v).filter (fun rho => alpha ≤ rho.re ∧ |rho.im| ≤ y) := by
    ext rho
    simp only [mem_zeroValues, Finset.mem_filter]
    constructor
    · rintro ⟨hz, ⟨h0, h1, hh⟩, hb⟩
      exact ⟨⟨hz, ⟨h0, h1, hh.trans hy⟩, ha.trans hb⟩, hb, hh⟩
    · rintro ⟨⟨hz, ⟨h0, h1, _⟩, _⟩, hb, hh⟩
      exact ⟨hz, ⟨h0, h1, hh⟩, hb⟩
  simp only [familyCount, count, hs, Nat.cast_sum, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hb : alpha ≤ rho.re <;> by_cases hh : |rho.im| ≤ y <;>
    simp [Set.indicator, hb, hh]
  ring

theorem density_rectangle_integrable {q : ℕ} [NeZero q] {x a b u v : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (hu : 0 < u) (huv : u ≤ v) :
    Integrable (fun p : ℝ × ℝ =>
      alphaKernel x p.1 * heightKernel p.2 * (familyCount q p.1 p.2 : ℝ))
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc u v))) := by
  have hc (chi : Character q) : Integrable (fun p : ℝ × ℝ =>
      ∑ rho ∈ zeroValues chi a v,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Iic rho.re).indicator (alphaKernel x) p.1) *
            (Set.Ici |rho.im|).indicator heightKernel p.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc u v))) := by
    apply integrable_finsetSum
    intro rho _
    have hi := ((alpha_indicator_integrable hx a b rho.re).const_mul
      (analyticOrderNatAt chi.LFunction rho : ℝ)).def'
    have hj := (heightKernel_closed_indicator_integrable hu huv |rho.im|).def'
    rw [Set.uIoc_of_le hab] at hi
    rw [Set.uIoc_of_le huv] at hj
    exact hi.mul_prod hj
  have hi := integrable_finsetSum (Finset.univ : Finset (Character q)) (fun chi _ => hc chi)
  apply hi.congr
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  intro p hp
  exact (density_rectangle_finite hp.1.1.le hp.2.2 x).symm

/-- The exchange of the two actual density integrals in (5.7). -/
theorem density_rectangle_swap {q : ℕ} [NeZero q] {x a b u v : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (hu : 0 < u) (huv : u ≤ v) :
    (∫ alpha in a..b, alphaKernel x alpha *
      ∫ y in u..v, heightKernel y * (familyCount q alpha y : ℝ)) =
      ∫ y in u..v, heightKernel y *
        ∫ alpha in a..b, alphaKernel x alpha * (familyCount q alpha y : ℝ) := by
  simp_rw [← intervalIntegral.integral_const_mul]
  have hf := density_rectangle_integrable (q := q) hx hab hu huv
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le huv]
  calc
    _ = ∫ alpha in Set.Ioc a b, ∫ y in Set.Ioc u v,
        alphaKernel x alpha * heightKernel y * (familyCount q alpha y : ℝ) := by
      apply integral_congr_ae
      filter_upwards with alpha
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y in Set.Ioc u v, ∫ alpha in Set.Ioc a b,
        alphaKernel x alpha * heightKernel y * (familyCount q alpha y : ℝ) :=
      integral_integral_swap hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with alpha
      ring

theorem density_alpha_outer_integrable {q : ℕ} [NeZero q] {x a b u v : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun alpha => alphaKernel x alpha *
      ∫ y in u..v, heightKernel y * (familyCount q alpha y : ℝ)) volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  have hf := (density_rectangle_integrable (q := q) hx hab hu huv).integral_prod_left
  apply hf.congr
  filter_upwards with alpha
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le huv]
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem alpha_height_reduction {q : ℕ} [NeZero q] {x a b u v : ℝ}
    (hx : 1 ≤ x) (hab : a ≤ b) (hu : 0 < u) (huv : u ≤ v) :
    (∫ alpha in a..b, alphaKernel x alpha * bandMass q alpha u v) ≤
      (1 / Real.sqrt v) *
        (∫ alpha in a..b, alphaKernel x alpha * (familyCount q alpha v : ℝ)) +
      (1 / 2 : ℝ) * ∫ y in u..v, heightKernel y *
        ∫ alpha in a..b, alphaKernel x alpha * (familyCount q alpha y : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h1 := (count_alpha_integrable (q := q) hx0 hab v).const_mul (1 / Real.sqrt v)
  have h2 := (density_alpha_outer_integrable (q := q) hx0 hab hu huv).const_mul (1 / 2 : ℝ)
  calc
    _ ≤ ∫ alpha in a..b,
        (1 / Real.sqrt v) * (alphaKernel x alpha * (familyCount q alpha v : ℝ)) +
        (1 / 2 : ℝ) * (alphaKernel x alpha *
          ∫ y in u..v, heightKernel y * (familyCount q alpha y : ℝ)) := by
      apply intervalIntegral.integral_mono_on hab
        (bandMass_alpha_integrable hx0 hab u v) (h1.add h2)
      intro alpha _
      have hp : 0 ≤ alphaKernel x alpha :=
        mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx)
      exact (mul_le_mul_of_nonneg_left (family_height_abel q alpha hu huv) hp).trans_eq
        (by ring)
    _ = _ := by
      rw [intervalIntegral.integral_add h1 h2]
      simp only [intervalIntegral.integral_const_mul]
      rw [density_rectangle_swap hx0 hab hu huv]

end LiuWang.Proof.SourceRoute.SecondArc
