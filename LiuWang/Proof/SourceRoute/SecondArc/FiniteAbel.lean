import LiuWang.Proof.SourceRoute.SecondArc.HeightKernel

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.SourceRoute.SecondArc

theorem heightKernel_closed_indicator_integrable {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (h : ℝ) :
    IntervalIntegrable ((Set.Ici h).indicator heightKernel) volume u v := by
  rw [intervalIntegrable_iff]
  exact (heightKernel_integrable hu huv).def'.indicator measurableSet_Ici

theorem heightKernel_closed_indicator {u h v : ℝ} (hu : 0 < u)
    (huh : u ≤ h) (hhv : h ≤ v) :
    (∫ y in u..v, (Set.Ici h).indicator heightKernel y) =
      2 * (1 / Real.sqrt h - 1 / Real.sqrt v) := by
  have he : (Set.Ioi h).indicator heightKernel =ᵐ[volume]
      (Set.Ici h).indicator heightKernel :=
    indicator_ae_eq_of_ae_eq_set Ioi_ae_eq_Ici
  calc
    _ = ∫ y in u..v, (Set.Ioi h).indicator heightKernel y :=
      intervalIntegral.integral_congr_ae (he.symm.mono (fun _ hy _ => hy))
    _ = _ := heightKernel_upper_indicator hu huh hhv

def cumulativeWeight {ι : Type*} (s : Finset ι) (h c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s.filter (fun i => h i ≤ y), c i

theorem height_integrand_eq_sum {ι : Type*} (s : Finset ι) (h c : ι → ℝ) (y : ℝ) :
    heightKernel y * cumulativeWeight s h c y =
      ∑ i ∈ s, c i * (Set.Ici (h i)).indicator heightKernel y := by
  simp only [cumulativeWeight, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : h i ≤ y <;> simp [Set.indicator, hi, mul_comm]

theorem height_integrand_integrable {ι : Type*} (s : Finset ι) (h c : ι → ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun y => heightKernel y * cumulativeWeight s h c y)
      volume u v := by
  simp_rw [height_integrand_eq_sum]
  convert! IntervalIntegrable.sum s (fun i _ =>
    (heightKernel_closed_indicator_integrable hu huv (h i)).const_mul (c i)) using 1
  ext y
  simp only [Finset.sum_apply]

theorem finite_height_abel {ι : Type*} (s : Finset ι) (h c : ι → ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hh : ∀ i ∈ s, u ≤ h i ∧ h i ≤ v) :
    (∑ i ∈ s, c i / Real.sqrt (h i)) =
      (∑ i ∈ s, c i) / Real.sqrt v +
        (1 / 2 : ℝ) * ∫ y in u..v, heightKernel y * cumulativeWeight s h c y := by
  simp_rw [height_integrand_eq_sum]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul]
    have he (i : ι) (hi : i ∈ s) :
        (∫ y in u..v, (Set.Ici (h i)).indicator heightKernel y) =
          2 * (1 / Real.sqrt (h i) - 1 / Real.sqrt v) :=
      heightKernel_closed_indicator hu (hh i hi).1 (hh i hi).2
    rw [Finset.sum_congr rfl (fun i hi => congrArg (c i * ·) (he i hi))]
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact (heightKernel_closed_indicator_integrable hu huv (h i)).const_mul (c i)

theorem cumulativeWeight_mono {ι : Type*} {s t : Finset ι} (h c : ι → ℝ)
    (hst : s ⊆ t) (hc : ∀ i ∈ t, 0 ≤ c i) (y : ℝ) :
    cumulativeWeight s h c y ≤ cumulativeWeight t h c y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ hst
  · intro i hi _
    exact hc i (Finset.mem_filter.mp hi).1

theorem finite_height_abel_le {ι : Type*} {s t : Finset ι} (h c : ι → ℝ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hst : s ⊆ t) (hc : ∀ i ∈ t, 0 ≤ c i)
    (hh : ∀ i ∈ s, u ≤ h i ∧ h i ≤ v) :
    (∑ i ∈ s, c i / Real.sqrt (h i)) ≤
      (∑ i ∈ t, c i) / Real.sqrt v +
        (1 / 2 : ℝ) * ∫ y in u..v, heightKernel y * cumulativeWeight t h c y := by
  rw [finite_height_abel s h c hu huv hh]
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i hi _ => hc i hi)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply intervalIntegral.integral_mono_on huv
      (height_integrand_integrable s h c hu huv)
      (height_integrand_integrable t h c hu huv)
    intro y hy
    exact mul_le_mul_of_nonneg_left (cumulativeWeight_mono h c hst hc y)
      (heightKernel_nonneg (hu.le.trans hy.1))

end LiuWang.Proof.SourceRoute.SecondArc
