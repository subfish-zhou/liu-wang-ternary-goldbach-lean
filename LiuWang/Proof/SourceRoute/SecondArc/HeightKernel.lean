import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc

def heightKernel (y : ℝ) : ℝ := y ^ (-3 / 2 : ℝ)

theorem heightKernel_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ heightKernel y :=
  Real.rpow_nonneg hy _

theorem heightKernel_integrable {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable heightKernel volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  exact continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hu.trans_le hy.1)))

theorem integral_heightKernel {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ y in u..v, heightKernel y) =
      2 * (1 / Real.sqrt u - 1 / Real.sqrt v) := by
  have hp : ∀ t : ℝ, 0 < t → t ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt t := by
    intro t ht
    simp only [Real.rpow_neg ht.le, Real.sqrt_eq_rpow, one_div]
  unfold heightKernel
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    rw [Set.uIcc_of_le huv]
    intro h
    exact (not_le_of_gt hu) h.1⟩)]
  norm_num
  rw [hp u hu, hp v (hu.trans_le huv)]
  ring

theorem heightKernel_indicator_integrable {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (h : ℝ) :
    IntervalIntegrable ((Set.Iic h).indicator heightKernel) volume u v := by
  rw [intervalIntegrable_iff]
  exact (heightKernel_integrable hu huv).def'.indicator measurableSet_Iic

theorem heightKernel_lower_indicator {u h v : ℝ} (hu : 0 < u)
    (huh : u ≤ h) (hhv : h ≤ v) :
    (∫ y in u..v, (Set.Iic h).indicator heightKernel y) =
      2 * (1 / Real.sqrt u - 1 / Real.sqrt h) := by
  calc
    _ = ∫ y in u..h, heightKernel y :=
      intervalIntegral.integral_indicator ⟨huh, hhv⟩
    _ = _ := integral_heightKernel hu huh

theorem heightKernel_upper_indicator_integrable {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (h : ℝ) :
    IntervalIntegrable ((Set.Ioi h).indicator heightKernel) volume u v := by
  rw [intervalIntegrable_iff]
  exact (heightKernel_integrable hu huv).def'.indicator measurableSet_Ioi

theorem heightKernel_upper_indicator {u h v : ℝ} (hu : 0 < u)
    (huh : u ≤ h) (hhv : h ≤ v) :
    (∫ y in u..v, (Set.Ioi h).indicator heightKernel y) =
      2 * (1 / Real.sqrt h - 1 / Real.sqrt v) := by
  have heq : (Set.Ioi h).indicator heightKernel =
      fun y => heightKernel y - (Set.Iic h).indicator heightKernel y := by
    funext y
    by_cases hy : y ≤ h
    · simp [Set.indicator, hy, not_lt.mpr hy]
    · simp [Set.indicator, hy, lt_of_not_ge hy]
  rw [heq, intervalIntegral.integral_sub
    (heightKernel_integrable hu (huh.trans hhv))
    (heightKernel_indicator_integrable hu (huh.trans hhv) h),
    integral_heightKernel hu (huh.trans hhv),
    heightKernel_lower_indicator hu huh hhv]
  ring

end LiuWang.Proof.SourceRoute.SecondArc
