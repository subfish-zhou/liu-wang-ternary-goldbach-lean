import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanShift

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem ordinate_step_monotone (g : ℝ) :
    Monotone (fun t : ℝ => if g ≤ t then (1 : ℝ) else 0) := by
  intro a b hab
  dsimp only
  split_ifs with ha hb
  · exact le_rfl
  · exact (hb (ha.trans hab)).elim
  · norm_num
  · exact le_rfl

theorem integral_ordinate_step {a b g : ℝ} (hab : a ≤ b) (hgb : g ≤ b) :
    (∫ t in a..b, if g ≤ t then (1 : ℝ) else 0) = b - max a g := by
  by_cases hga : g ≤ a
  · rw [max_eq_left hga]
    have he : (∫ t in a..b, if g ≤ t then (1 : ℝ) else 0) = ∫ _t in a..b, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      simp [hga.trans ht.1]
    rw [he]
    simp
  · have hag : a ≤ g := (not_le.mp hga).le
    rw [max_eq_right hag]
    have hl : (∫ t in a..g, if g ≤ t then (1 : ℝ) else 0) = 0 := by
      have he : (∫ t in a..g, if g ≤ t then (1 : ℝ) else 0) = ∫ _t in a..g, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hag
        intro t ht
        simp [not_le.mpr ht.2]
      simpa using he
    have hr : (∫ t in g..b, if g ≤ t then (1 : ℝ) else 0) = b - g := by
      have he : (∫ t in g..b, if g ≤ t then (1 : ℝ) else 0) = ∫ _t in g..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hgb
        intro t ht
        simp [ht.1.le]
      simpa using he
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      ((ordinate_step_monotone g).intervalIntegrable (μ := volume) (a := a) (b := g))
      ((ordinate_step_monotone g).intervalIntegrable (μ := volume) (a := g) (b := b))
    rw [hl, hr, zero_add] at hadd
    exact hadd.symm

theorem positiveCount_eq_finite_steps {t b : ℝ} (htb : t ≤ b) :
    (positiveCount t : ℝ) =
      ∑ z ∈ positiveValues b, (analyticOrderNatAt riemannZeta z : ℝ) *
        (if z.im ≤ t then (1 : ℝ) else 0) := by
  classical
  have he : positiveValues t = (positiveValues b).filter (fun z => z.im ≤ t) := by
    ext z
    rw [Finset.mem_filter, mem_positiveValues, mem_positiveValues]
    constructor
    · rintro ⟨hz, h0, h1, hp, ht⟩
      exact ⟨⟨hz, h0, h1, hp, ht.trans htb⟩, ht⟩
    · rintro ⟨⟨hz, h0, h1, hp, _⟩, ht⟩
      exact ⟨hz, h0, h1, hp, ht⟩
  rw [positiveCount, he]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

theorem integral_positiveCount_eq_zero_areas {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, (positiveCount t : ℝ)) =
      ∑ z ∈ positiveValues b, (analyticOrderNatAt riemannZeta z : ℝ) *
        (b - max a z.im) := by
  classical
  have he : (∫ t in a..b, (positiveCount t : ℝ)) =
      ∫ t in a..b, ∑ z ∈ positiveValues b, (analyticOrderNatAt riemannZeta z : ℝ) *
        (if z.im ≤ t then (1 : ℝ) else 0) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact positiveCount_eq_finite_steps ht.2
  rw [he, intervalIntegral.integral_finsetSum (fun z _ =>
    (ordinate_step_monotone z.im).intervalIntegrable.const_mul _)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [intervalIntegral.integral_const_mul,
    integral_ordinate_step hab (mem_positiveValues.mp hz).2.2.2.2]

theorem integral_turingS_eq_zero_areas {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, turingS t) =
      (∑ z ∈ positiveValues b, (analyticOrderNatAt riemannZeta z : ℝ) *
        (b - max a z.im)) - (b - a) -
          (∫ t in a..b, criticalGammaArgument t) / Real.pi := by
  unfold turingS
  rw [intervalIntegral.integral_sub
    ((positiveCount_intervalIntegrable a b).sub intervalIntegrable_const)
    ((criticalGammaArgument_continuous.intervalIntegrable a b).div_const _),
    intervalIntegral.integral_sub (positiveCount_intervalIntegrable a b) intervalIntegrable_const,
    integral_positiveCount_eq_zero_areas hab, intervalIntegral.integral_const,
    intervalIntegral.integral_div]
  simp

theorem zero_area_lower_bound {a b : ℝ} (hab : a ≤ b) (F : Finset ℂ)
    (hF : F ⊆ positiveValues b) :
    (∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (b - max a z.im)) ≤
      (∫ t in a..b, turingS t) + (b - a) +
        (∫ t in a..b, criticalGammaArgument t) / Real.pi := by
  rw [integral_turingS_eq_zero_areas hab]
  have hc (X Y Z : ℝ) : X - Y - Z + Y + Z = X := by ring
  rw [hc]
  apply Finset.sum_le_sum_of_subset_of_nonneg hF
  intro z hz _
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr
    (max_le hab (mem_positiveValues.mp hz).2.2.2.2))

#print axioms integral_positiveCount_eq_zero_areas
#print axioms integral_turingS_eq_zero_areas
#print axioms zero_area_lower_bound

end LiuWang.Proof.Campaign20260915.ZetaWinding
