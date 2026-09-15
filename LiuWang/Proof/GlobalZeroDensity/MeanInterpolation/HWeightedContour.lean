import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HZetaCount
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Foundations

/-! The actual horizontal-distance weighted detector argument principle. -/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped Topology

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

def weightedDetectorKernel (y : ℝ) (c s : ℂ) : ℂ :=
  (s - c) * logDeriv (entireH y) s

theorem entireH_meromorphicOrder {y : ℝ} (hy : 3 < y) (s : ℂ) :
    meromorphicOrderAt (entireH y) s = ((analyticOrderNatAt (entireH y) s : ℤ) : WithTop ℤ) := by
  rw [(analytic_entireH y s).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (entireH_order_finite hy s)]
  simp

theorem weightedDetector_residue {y : ℝ} (hy : 3 < y) (c s : ℂ) :
    residue (weightedDetectorKernel y c) s =
      (s - c) * (analyticOrderNatAt (entireH y) s : ℂ) := by
  have hr := Kadiri.residue_mul_eq_of_sub_principal_isBigO_one
    (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
      (analytic_entireH y s).meromorphicAt (entireH_meromorphicOrder hy s))
    (Ψ := fun z : ℂ => z - c) (by fun_prop)
  change residue (fun z : ℂ => (z - c) * logDeriv (entireH y) z) s = _
  simpa only [mul_comm, Int.cast_natCast] using hr

theorem analytic_weightedDetector {y : ℝ} {c s : ℂ} (hs : entireH y s ≠ 0) :
    AnalyticAt ℂ (weightedDetectorKernel y c) s :=
  (analyticAt_id.sub analyticAt_const).mul
    ((analytic_entireH y s).deriv.div (analytic_entireH y s) hs)

theorem weightedDetector_poles {y : ℝ} (hy : 3 < y) {c : ℂ} (hc : entireH y c ≠ 0)
    (U : Set ℂ) :
    U ∩ {s | meromorphicOrderAt (weightedDetectorKernel y c) s < 0} =
      (MeromorphicOn.divisor (entireH y) U).support := by
  have hm : MeromorphicOn (entireH y) U := fun s _ => (analytic_entireH y s).meromorphicAt
  rw [← logDeriv_poles_eq_divisor_support hm hm.logDeriv
    (fun s _ => by rw [entireH_meromorphicOrder hy]; simp)]
  ext s
  by_cases hs : s = c
  · subst s
    have ha := analytic_weightedDetector (c := c) hc
    have hb : AnalyticAt ℂ (logDeriv (entireH y)) c :=
      (analytic_entireH y c).deriv.div (analytic_entireH y c) hc
    simp only [mem_inter_iff, mem_ofPred_eq,
      not_lt.mpr ha.meromorphicOrderAt_nonneg, not_lt.mpr hb.meromorphicOrderAt_nonneg]
  · have he : meromorphicOrderAt (weightedDetectorKernel y c) s =
        meromorphicOrderAt (logDeriv (entireH y)) s :=
      meromorphicOrderAt_mul_of_ne_zero (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - c) s)
        (sub_ne_zero.mpr hs)
    simp only [mem_inter_iff, mem_ofPred_eq, he]

theorem weightedDetector_simple {y : ℝ} (hy : 3 < y) {c : ℂ} (hc : entireH y c ≠ 0)
    (U : Set ℂ) : HasSimplePolesOn (weightedDetectorKernel y c) U := by
  have hm : MeromorphicOn (entireH y) U := fun s _ => (analytic_entireH y s).meromorphicAt
  have hl := logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top hm hm.logDeriv
    (fun s _ => by rw [entireH_meromorphicOrder hy]; simp)
  intro s hs
  by_cases hsc : s = c
  · subst s
    exact le_trans (WithTop.coe_le_coe.mpr (by norm_num : (-1 : ℤ) ≤ 0))
      (analytic_weightedDetector (c := c) hc).meromorphicOrderAt_nonneg
  · change (-1 : ℤ) ≤ meromorphicOrderAt ((fun z : ℂ => z - c) * logDeriv (entireH y)) s
    rw [meromorphicOrderAt_mul_of_ne_zero
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - c) s) (sub_ne_zero.mpr hsc)]
    exact hl s hs

theorem weightedDetector_integrable {y : ℝ} {c z w : ℂ}
    (hb : ∀ s ∈ RectangleBorder z w, entireH y s ≠ 0) :
    RectangleBorderIntegrable (weightedDetectorKernel y c) z w :=
  ContinuousOn.rectangleBorder_integrable
    (fun s hs => (analytic_weightedDetector (c := c) (hb s hs)).continuousAt.continuousWithinAt)

theorem weightedDetector_rectangle {y : ℝ} (hy : 3 < y) {c z w : ℂ}
    (hc : entireH y c ≠ 0) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, entireH y s ≠ 0) :
    RectangleIntegral' (weightedDetectorKernel y c) z w =
      ∑ s ∈ (divisor_support_rectangle_finite (entireH y) z w).toFinset,
        (s - c) * (analyticOrderNatAt (entireH y) s : ℂ) := by
  have hm0 : MeromorphicOn (entireH y) univ := fun s _ => (analytic_entireH y s).meromorphicAt
  have hm : MeromorphicOn (weightedDetectorKernel y c) (Rectangle z w) :=
    fun s _ => (by fun_prop : MeromorphicAt (fun z : ℂ => z - c) s).mul
      (hm0.logDeriv s (mem_univ s))
  have hp := weightedDetector_poles hy hc (Rectangle z w)
  have hf : (Rectangle z w ∩
      {s | meromorphicOrderAt (weightedDetectorKernel y c) s < 0}).Finite := by
    rw [hp]
    exact divisor_support_rectangle_finite (entireH y) z w
  have hn : Disjoint (RectangleBorder z w)
      {s | meromorphicOrderAt (weightedDetectorKernel y c) s < 0} := by
    rw [Set.disjoint_left]
    intro s hs hpole
    exact not_lt.mpr (analytic_weightedDetector (c := c) (hb s hs)).meromorphicOrderAt_nonneg hpole
  rw [RectangleIntegral'_eq_sumResiduesIn hre him hm hn hf (weightedDetector_simple hy hc _),
    hp, sumResiduesIn]
  have hfin := divisor_support_rectangle_finite (entireH y) z w
  have hsum : (∑' s : (MeromorphicOn.divisor (entireH y) (Rectangle z w)).support,
      residue (weightedDetectorKernel y c) s) =
      ∑ s ∈ hfin.toFinset, residue (weightedDetectorKernel y c) s := by
    let D := hfin.toFinset
    change _ = ∑ s ∈ D, residue (weightedDetectorKernel y c) s
    have he : (MeromorphicOn.divisor (entireH y) (Rectangle z w)).support = (D : Set ℂ) :=
      hfin.coe_toFinset.symm
    rw [he, tsum_fintype, ← Finset.sum_coe_sort D]
    rfl
  rw [hsum]
  apply Finset.sum_congr rfl
  intro s _
  exact weightedDetector_residue hy c s

theorem weightedDetector_rectangle_re {y : ℝ} (hy : 3 < y) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, entireH y s ≠ 0) :
    (RectangleIntegral' (weightedDetectorKernel y z) z w).re =
      ∑ s ∈ (divisor_support_rectangle_finite (entireH y) z w).toFinset,
        (s.re - z.re) * (analyticOrderNatAt (entireH y) s : ℝ) := by
  have hz : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  rw [weightedDetector_rectangle hy (hb z hz) hre him hb, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
