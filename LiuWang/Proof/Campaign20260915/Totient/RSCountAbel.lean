import LiuWang.Proof.Campaign20260915.ZetaWinding.CountingIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set Finset
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPositiveWindowSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ z ∈ (positiveValues b).filter (fun z => a < z.im),
    (analyticOrderNatAt riemannZeta z : ℝ) * f z.im

theorem rs_integral_weighted_step {a b g : ℝ} (hab : a ≤ b) (hgb : g ≤ b)
    {f f' : ℝ → ℝ} (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Icc a b)) :
    (∫ t in a..b, (if g ≤ t then (1 : ℝ) else 0) * f' t) =
      f b - f (max a g) := by
  have hc' : ContinuousOn f' (uIcc a b) := by rwa [uIcc_of_le hab]
  by_cases hga : g ≤ a
  · rw [max_eq_left hga]
    calc
      _ = ∫ t in a..b, f' t := intervalIntegral.integral_congr (fun t ht => by
        rw [uIcc_of_le hab] at ht
        simp only [if_pos (hga.trans ht.1), one_mul])
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hd t (by simpa only [uIcc_of_le hab] using ht)) hc'.intervalIntegrable
  · have hag := (lt_of_not_ge hga).le
    rw [max_eq_right hag]
    have hl : (∫ t in a..g, (if g ≤ t then (1 : ℝ) else 0) * f' t) = 0 := by
      calc
        _ = ∫ _t in a..g, (0 : ℝ) := intervalIntegral.integral_congr_Ioo_of_le hag
          (fun t ht => by simp only [if_neg (not_le.mpr ht.2), zero_mul])
        _ = 0 := by simp
    have hr : (∫ t in g..b, (if g ≤ t then (1 : ℝ) else 0) * f' t) = f b - f g := by
      calc
        _ = ∫ t in g..b, f' t := intervalIntegral.integral_congr (fun t ht => by
          rw [uIcc_of_le hgb] at ht
          simp only [if_pos ht.1, one_mul])
        _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => hd t (by
            rw [uIcc_of_le hgb] at ht
            exact ⟨hag.trans ht.1, ht.2⟩))
          ((hc.mono (fun t ht => by
            rw [uIcc_of_le hgb] at ht
            exact ⟨hag.trans ht.1, ht.2⟩)).intervalIntegrable)
    have hi := ((ordinate_step_monotone g).intervalIntegrable (μ := volume)
      (a := a) (b := b)).mul_continuousOn hc'
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hi.mono_set (by
        rw [uIcc_of_le hag, uIcc_of_le hab]
        exact Icc_subset_Icc le_rfl hgb))
      (hi.mono_set (by
        rw [uIcc_of_le hgb, uIcc_of_le hab]
        exact Icc_subset_Icc hag le_rfl))
    rw [hl, hr, zero_add] at hs
    exact hs.symm

theorem rs_positiveCount_weighted_integral {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℝ} (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Icc a b)) :
    (∫ t in a..b, (positiveCount t : ℝ) * f' t) =
      ∑ z ∈ positiveValues b, (analyticOrderNatAt riemannZeta z : ℝ) *
        (f b - f (max a z.im)) := by
  have hc' : ContinuousOn f' (uIcc a b) := by rwa [uIcc_of_le hab]
  calc
    _ = ∫ t in a..b, ∑ z ∈ positiveValues b,
        (analyticOrderNatAt riemannZeta z : ℝ) *
          ((if z.im ≤ t then (1 : ℝ) else 0) * f' t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [positiveCount_eq_finite_steps ht.2, sum_mul]
      exact sum_congr rfl (fun _ _ => mul_assoc _ _ _)
    _ = ∑ z ∈ positiveValues b, (analyticOrderNatAt riemannZeta z : ℝ) *
        (f b - f (max a z.im)) := by
      rw [intervalIntegral.integral_finsetSum (fun z _ =>
        (((ordinate_step_monotone z.im).intervalIntegrable).mul_continuousOn hc').const_mul _)]
      apply sum_congr rfl
      intro z hz
      rw [intervalIntegral.integral_const_mul,
        rs_integral_weighted_step hab (mem_positiveValues.mp hz).2.2.2.2 hd hc]

theorem rs_positiveCount_abel {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℝ} (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Icc a b)) :
    rsPositiveWindowSum f a b =
      (positiveCount b : ℝ) * f b - (positiveCount a : ℝ) * f a -
        ∫ t in a..b, (positiveCount t : ℝ) * f' t := by
  classical
  rw [rs_positiveCount_weighted_integral hab hd hc,
    positiveCount_eq_finite_steps hab, positiveCount_eq_finite_steps (le_refl b)]
  simp only [sum_mul, ← sum_sub_distrib]
  unfold rsPositiveWindowSum
  rw [sum_filter]
  apply sum_congr rfl
  intro z hz
  have hzb := (mem_positiveValues.mp hz).2.2.2.2
  by_cases hza : a < z.im
  · simp only [if_pos hzb, if_neg (not_le.mpr hza), if_pos hza,
      max_eq_right hza.le, mul_one, mul_zero, zero_mul]
    ring
  · simp only [if_pos hzb, if_pos (le_of_not_gt hza), if_neg hza,
      max_eq_left (le_of_not_gt hza), mul_one]
    ring

#print axioms rs_integral_weighted_step
#print axioms rs_positiveCount_weighted_integral
#print axioms rs_positiveCount_abel

end LiuWang.Proof.Campaign20260915.Totient
