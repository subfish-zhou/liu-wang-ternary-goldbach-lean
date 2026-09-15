import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ActualCount
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation

theorem integral_alpha_indicator_clipped {x a b : ℝ} (hx : 0 < x) (hab : a ≤ b)
    (beta : ℝ) :
    (∫ alpha in a..b, (Set.Iic beta).indicator (alphaKernel x) alpha) =
      x ^ (min b beta - 1) - x ^ (min a beta - 1) := by
  by_cases hba : beta ≤ a
  · rw [min_eq_right (hba.trans hab), min_eq_right hba, sub_self]
    apply intervalIntegral.integral_zero_ae
    filter_upwards with alpha
    intro ha
    rw [Set.uIoc_of_le hab] at ha
    exact Set.indicator_of_notMem (by
      exact not_le.mpr (hba.trans_lt ha.1) : alpha ∉ Set.Iic beta) _
  · have habeta : a ≤ beta := (lt_of_not_ge hba).le
    rw [min_eq_left habeta]
    by_cases hbb : beta ≤ b
    · rw [min_eq_right hbb]
      exact alpha_indicator_integral hx habeta hbb
    · rw [min_eq_left (le_of_not_ge hbb)]
      calc
        _ = ∫ alpha in a..b, alphaKernel x alpha := by
          apply intervalIntegral.integral_congr
          intro alpha ha
          rw [Set.uIcc_of_le hab] at ha
          exact Set.indicator_of_mem
            (show alpha ∈ Set.Iic beta from ha.2.trans (le_of_not_ge hbb)) _
        _ = _ := integral_alphaKernel hx a b

theorem count_strip_finite {q : ℕ} [NeZero q] {x a b v y : ℝ}
    (hx : 0 < x) (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hy : y ≤ v) :
    (∫ alpha in a..b, alphaKernel x alpha * (familyCount q alpha y : ℝ)) =
      ∑ chi : Character q, ∑ rho ∈ zeroValues chi (1 / 2) v,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Ici |rho.im|).indicator
            (fun _ => x ^ (min b rho.re - 1) - x ^ (min a rho.re - 1)) y := by
  have hs (chi : Character q) (alpha : ℝ) (halpha : a ≤ alpha) :
      zeroValues chi alpha y =
        (zeroValues chi (1 / 2) v).filter (fun rho => alpha ≤ rho.re ∧ |rho.im| ≤ y) := by
    ext rho
    simp only [Finset.mem_filter, mem_zeroValues]
    constructor
    · rintro ⟨hz, ⟨h0, h1, ht⟩, hb⟩
      exact ⟨⟨hz, ⟨h0, h1, ht.trans hy⟩, ha.trans (halpha.trans hb)⟩, hb, ht⟩
    · rintro ⟨⟨hz, ⟨h0, h1, _⟩, _⟩, hb, ht⟩
      exact ⟨hz, ⟨h0, h1, ht⟩, hb⟩
  have he (alpha : ℝ) (halpha : a ≤ alpha) :
      alphaKernel x alpha * (familyCount q alpha y : ℝ) =
        ∑ chi : Character q, ∑ rho ∈ zeroValues chi (1 / 2) v,
          (analyticOrderNatAt chi.LFunction rho : ℝ) *
            (if |rho.im| ≤ y then (Set.Iic rho.re).indicator (alphaKernel x) alpha else 0) := by
    simp only [familyCount, count, hs _ alpha halpha, Nat.cast_sum,
      Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi _
    apply Finset.sum_congr rfl
    intro rho _
    by_cases hr : alpha ≤ rho.re <;> by_cases hh : |rho.im| ≤ y <;>
      simp [Set.indicator, hr, hh, mul_comm]
  have hi (chi : Character q) (rho : ℂ) : IntervalIntegrable (fun alpha =>
      (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (if |rho.im| ≤ y then (Set.Iic rho.re).indicator (alphaKernel x) alpha else 0))
      volume a b := by
    by_cases hh : |rho.im| ≤ y
    · simpa only [hh, if_true] using
        (alpha_indicator_integrable hx a b rho.re).const_mul
          (analyticOrderNatAt chi.LFunction rho : ℝ)
    · simp only [hh, if_false, mul_zero]
      exact intervalIntegrable_const
  have hc (chi : Character q) : IntervalIntegrable (fun alpha =>
      ∑ rho ∈ zeroValues chi (1 / 2) v, (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (if |rho.im| ≤ y then (Set.Iic rho.re).indicator (alphaKernel x) alpha else 0))
      volume a b := by
    convert! IntervalIntegrable.sum (zeroValues chi (1 / 2) v) (fun rho _ => hi chi rho) using 1
    ext alpha
    simp only [Finset.sum_apply]
  calc
    _ = ∫ alpha in a..b, ∑ chi : Character q, ∑ rho ∈ zeroValues chi (1 / 2) v,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (if |rho.im| ≤ y then (Set.Iic rho.re).indicator (alphaKernel x) alpha else 0) := by
      apply intervalIntegral.integral_congr
      intro alpha halpha
      rw [Set.uIcc_of_le hab] at halpha
      exact he alpha halpha.1
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun chi _ => hc chi)]
      apply Finset.sum_congr rfl
      intro chi _
      rw [intervalIntegral.integral_finsetSum (fun rho _ => hi chi rho)]
      apply Finset.sum_congr rfl
      intro rho _
      by_cases hh : |rho.im| ≤ y
      · simp only [hh, if_true, Set.indicator_of_mem (show y ∈ Set.Ici |rho.im| from hh)]
        rw [intervalIntegral.integral_const_mul, integral_alpha_indicator_clipped hx hab]
      · simp [hh, Set.indicator_of_notMem]

theorem moving_count_strip_integrable {q : ℕ} [NeZero q] {x u v : ℝ}
    {a b : ℝ → ℝ} (hx : 0 < x) (huv : u ≤ v)
    (ha : ContinuousOn a (Set.Icc u v)) (hb : ContinuousOn b (Set.Icc u v))
    (ha0 : ∀ y ∈ Set.Icc u v, 1 / 2 ≤ a y)
    (hab : ∀ y ∈ Set.Icc u v, a y ≤ b y) :
    IntervalIntegrable (fun y => ∫ alpha in (a y)..(b y),
      alphaKernel x alpha * (familyCount q alpha y : ℝ)) volume u v := by
  have hc (chi : Character q) (rho : ℂ) : IntervalIntegrable (fun y =>
      (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (Set.Ici |rho.im|).indicator
          (fun y => x ^ (min (b y) rho.re - 1) - x ^ (min (a y) rho.re - 1)) y)
      volume u v := by
    have ht : ContinuousOn
        (fun y => x ^ (min (b y) rho.re - 1) - x ^ (min (a y) rho.re - 1))
        (Set.Icc u v) :=
      ((Real.continuous_const_rpow hx.ne').comp_continuousOn
        ((hb.inf continuousOn_const).sub continuousOn_const)).sub
        ((Real.continuous_const_rpow hx.ne').comp_continuousOn
          ((ha.inf continuousOn_const).sub continuousOn_const))
    have hi := ht.intervalIntegrable_of_Icc (μ := volume) huv
    rw [intervalIntegrable_iff] at hi ⊢
    exact (hi.indicator measurableSet_Ici).const_mul _
  have hi : IntervalIntegrable (fun y => ∑ chi : Character q,
      ∑ rho ∈ zeroValues chi (1 / 2) v,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Ici |rho.im|).indicator
            (fun y => x ^ (min (b y) rho.re - 1) - x ^ (min (a y) rho.re - 1)) y)
      volume u v := by
    have hh (chi : Character q) : IntervalIntegrable (fun y =>
        ∑ rho ∈ zeroValues chi (1 / 2) v, (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Ici |rho.im|).indicator
            (fun y => x ^ (min (b y) rho.re - 1) - x ^ (min (a y) rho.re - 1)) y)
        volume u v := by
      convert! IntervalIntegrable.sum (zeroValues chi (1 / 2) v) (fun rho _ => hc chi rho) using 1
      ext y
      simp only [Finset.sum_apply]
    convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q)) (fun chi _ => hh chi) using 1
    ext y
    simp only [Finset.sum_apply]
  apply hi.congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huv] at hy
  have hy' : y ∈ Set.Icc u v := ⟨hy.1.le, hy.2⟩
  simpa only [Set.indicator] using
    (count_strip_finite hx (ha0 y hy') (hab y hy') hy.2).symm

end LiuWang.Proof.SourceRoute.SecondArc.Continuation
