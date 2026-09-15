import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HLogIntegral
import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Entire H regularization, finite actual multiplicities, and faithful local divisor counts. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

def entireH (y : ℝ) (s : ℂ) : ℂ := (s - 1) ^ 2 - regularNumerator y s ^ 2

theorem entireH_eq {s : ℂ} (hs : s ≠ 1) (y : ℝ) :
    entireH y s = (s - 1) ^ 2 * H y s := by
  rw [entireH, regularNumerator_eq hs, H]
  ring

theorem differentiable_entireH (y : ℝ) : Differentiable ℂ (entireH y) :=
  ((differentiable_id.sub_const 1).pow 2).sub ((differentiable_regularNumerator y).pow 2)

theorem analytic_entireH (y : ℝ) (s : ℂ) : AnalyticAt ℂ (entireH y) s :=
  (differentiable_entireH y).analyticAt s

theorem entireH_one (y : ℝ) : entireH y 1 = -(Q y 1) ^ 2 := by
  simp [entireH, regularNumerator, Complex.zetaTimesSMinusOne_entire_one]

theorem entireH_two_ne_zero {y : ℝ} (hy : 3 < y) : entireH y 2 ≠ 0 := by
  rw [entireH_eq (by norm_num)]
  exact mul_ne_zero (by norm_num) (H_ne_zero_on_two (by norm_num) hy)

theorem entireH_order_finite {y : ℝ} (hy : 3 < y) (s : ℂ) :
    analyticOrderAt (entireH y) s ≠ ⊤ := by
  have htwo : analyticOrderAt (entireH y) 2 = 0 :=
    (analytic_entireH y 2).analyticOrderAt_eq_zero.mpr (entireH_two_ne_zero hy)
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (f := entireH y) (U := univ) (fun z _ => analytic_entireH y z)
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) (by rw [htwo]; simp)

theorem entireH_order_eq_H {s : ℂ} (hs : s ≠ 1) (y : ℝ) :
    analyticOrderAt (entireH y) s = analyticOrderAt (H y) s := by
  have he : entireH y =ᶠ[𝓝 s] (fun z : ℂ => (z - 1) ^ 2) * H y := by
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact entireH_eq hz y
  have hp : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ 2) s := by fun_prop
  have hH : AnalyticAt ℂ (H y) s :=
    analyticAt_const.sub ((((analytic_zeta s hs).mul ((differentiable_Q y).analyticAt s)).sub
      analyticAt_const).pow 2)
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hp hH,
    hp.analyticOrderAt_eq_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hs)), zero_add]

theorem zeta_order_le_entireH {s : ℂ} (hs : s ≠ 1) (y : ℝ) :
    analyticOrderAt riemannZeta s ≤ analyticOrderAt (entireH y) s := by
  rw [entireH_order_eq_H hs]
  exact analyticOrder_H_ge_zeta y hs

theorem zeta_order_finite {y : ℝ} (hy : 3 < y) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ :=
  ne_top_of_le_ne_top (entireH_order_finite hy s) (zeta_order_le_entireH hs y)

theorem zeta_multiplicity_le {y : ℝ} (hy : 3 < y) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt riemannZeta s ≤ analyticOrderNatAt (entireH y) s := by
  have h := zeta_order_le_entireH hs y
  rw [← Nat.cast_analyticOrderNatAt (zeta_order_finite hy hs),
    ← Nat.cast_analyticOrderNatAt (entireH_order_finite hy s)] at h
  exact_mod_cast h

theorem entireH_divisor_apply {y : ℝ} (hy : 3 < y) {U : Set ℂ} {s : ℂ} (hs : s ∈ U) :
    MeromorphicOn.divisor (entireH y) U s = (analyticOrderNatAt (entireH y) s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (fun z _ => analytic_entireH y z) hs,
    ← Nat.cast_analyticOrderNatAt (entireH_order_finite hy s)]
  simp

theorem entireH_divisor_support {y : ℝ} (hy : 3 < y) (U : Set ℂ) :
    (MeromorphicOn.divisor (entireH y) U).support = {s ∈ U | entireH y s = 0} := by
  ext s
  by_cases hs : s ∈ U
  · rw [Function.mem_support, entireH_divisor_apply hy hs]
    have ho := (analytic_entireH y s).analyticOrderAt_eq_zero
    rw [← Nat.cast_analyticOrderNatAt (entireH_order_finite hy s)] at ho
    simp only [Nat.cast_eq_zero] at ho
    simp only [mem_ofPred_eq, hs, true_and]
    have hn : analyticOrderNatAt (entireH y) s ≠ 0 ↔ entireH y s = 0 := by tauto
    exact_mod_cast hn
  · have hnot : s ∉ (MeromorphicOn.divisor (entireH y) U).support :=
      fun h => hs ((MeromorphicOn.divisor (entireH y) U).supportWithinDomain h)
    simp [hnot, hs]

theorem entireH_zeros_finite {y : ℝ} (hy : 3 < y) {K : Set ℂ} (hK : IsCompact K) :
    {s ∈ K | entireH y s = 0}.Finite := by
  rw [← entireH_divisor_support hy K]
  exact (MeromorphicOn.divisor (entireH y) K).finiteSupport hK

def detectorCount (y : ℝ) (z w : ℂ) : ℕ :=
  ∑ s ∈ (divisor_support_rectangle_finite (entireH y) z w).toFinset,
    analyticOrderNatAt (entireH y) s

theorem detectorCount_divisor {y : ℝ} (hy : 3 < y) (z w : ℂ) :
    (detectorCount y z w : ℂ) =
      ∑ s ∈ (divisor_support_rectangle_finite (entireH y) z w).toFinset,
        (MeromorphicOn.divisor (entireH y) (Rectangle z w) s : ℂ) := by
  simp only [detectorCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsm := (divisor_support_rectangle_finite (entireH y) z w).mem_toFinset.mp hs
  rw [entireH_divisor_apply hy ((MeromorphicOn.divisor (entireH y) (Rectangle z w)).supportWithinDomain hsm)]
  simp

theorem zeta_finite_sum_le_detectorCount {y : ℝ} (hy : 3 < y) {z w : ℂ}
    (S : Finset ℂ) (hS : ∀ s ∈ S, s ∈ Rectangle z w ∧ s ≠ 1) :
    (∑ s ∈ S, analyticOrderNatAt riemannZeta s) ≤ detectorCount y z w := by
  classical
  let D := (divisor_support_rectangle_finite (entireH y) z w).toFinset
  have hcomp := Finset.sum_le_sum (fun s hs => zeta_multiplicity_le hy (hS s hs).2)
  apply hcomp.trans
  change (∑ s ∈ S, analyticOrderNatAt (entireH y) s) ≤ ∑ s ∈ D, analyticOrderNatAt (entireH y) s
  apply Finset.sum_le_sum_of_ne_zero
  intro s hs hne
  have hsupp : s ∈ (MeromorphicOn.divisor (entireH y) (Rectangle z w)).support := by
    rw [Function.mem_support, entireH_divisor_apply hy (hS s hs).1]
    exact_mod_cast hne
  exact (divisor_support_rectangle_finite (entireH y) z w).mem_toFinset.mpr hsupp

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
