import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HWeightedContour

/-! A paid delta-times-actual-zeta-count input to Littlewood, retaining closed boundaries. -/

set_option autoImplicit false

noncomputable section

open Complex Set

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem weighted_zeta_sum_le {y d : ℝ} (hy : 3 < y) (hd : 0 ≤ d) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, entireH y s ≠ 0)
    (S : Finset ℂ) (hS : ∀ s ∈ S,
      s ∈ Rectangle z w ∧ s ≠ 1 ∧ riemannZeta s = 0 ∧ z.re + d ≤ s.re) :
    d * (∑ s ∈ S, analyticOrderNatAt riemannZeta s : ℕ) ≤
      (RectangleIntegral' (weightedDetectorKernel y z) z w).re := by
  classical
  let D := (divisor_support_rectangle_finite (entireH y) z w).toFinset
  have hsub : S ⊆ D := by
    intro s hs
    obtain ⟨hsR, hs1, hsz, _⟩ := hS s hs
    apply (divisor_support_rectangle_finite (entireH y) z w).mem_toFinset.mpr
    rw [entireH_divisor_support hy]
    refine ⟨hsR, ?_⟩
    rw [entireH_eq hs1, H_factorization, hsz]
    simp
  rw [weightedDetector_rectangle_re hy hre him hb]
  simp only [Nat.cast_sum, Finset.mul_sum]
  apply le_trans (b := ∑ s ∈ S, (s.re - z.re) * (analyticOrderNatAt (entireH y) s : ℝ))
  · apply Finset.sum_le_sum
    intro s hs
    have hm : (analyticOrderNatAt riemannZeta s : ℝ) ≤
        (analyticOrderNatAt (entireH y) s : ℝ) := by
      exact_mod_cast zeta_multiplicity_le hy (hS s hs).2.1
    exact mul_le_mul (by linarith [(hS s hs).2.2.2]) hm (by positivity) (by linarith [(hS s hs).2.2.2])
  · apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro s hs _
    have hsR := (MeromorphicOn.divisor (entireH y) (Rectangle z w)).supportWithinDomain
      ((divisor_support_rectangle_finite (entireH y) z w).mem_toFinset.mp hs)
    exact mul_nonneg (sub_nonneg.mpr ((mem_Rect hre him s).mp hsR).1) (Nat.cast_nonneg _)

theorem closed_zeta_weighted_detection {y α T d ε : ℝ} (hy : 3 < y)
    (hα : α ≤ 2) (hT : 0 ≤ T) (hd : 0 < d) (hε : 0 < ε) :
    ∃ a ∈ Ioo (α - d - ε) (α - d), ∃ U ∈ Ioo T (T + ε),
      (∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) ∧
      RectangleBorderIntegrable (weightedDetectorKernel y ((a : ℂ) - U * I))
        ((a : ℂ) - U * I) ((2 : ℂ) + U * I) ∧
      d * (zetaDetectorRectangleCount ((α : ℂ) - T * I) ((2 : ℂ) + T * I) : ℝ) ≤
        (RectangleIntegral' (weightedDetectorKernel y ((a : ℂ) - U * I))
          ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re := by
  obtain ⟨a, ha, U, hU, hb⟩ := entireH_boundary_perturbation hy hε (a := α - d) (T := T)
  have hre : (((a : ℂ) - U * I)).re ≤ (((2 : ℂ) + U * I)).re := by
    simpa using (show a ≤ 2 by linarith [ha.2])
  have him : (((a : ℂ) - U * I)).im ≤ (((2 : ℂ) + U * I)).im := by
    simpa using (show -U ≤ U by linarith [hU.1])
  refine ⟨a, ha, U, hU, hb, weightedDetector_integrable hb, ?_⟩
  apply weighted_zeta_sum_le hy hd.le hre him hb
  intro s hs
  have hs0 := (zeta_rectangle_zeros_finite ((α : ℂ) - T * I)
    ((2 : ℂ) + T * I)).mem_toFinset.mp hs
  have hr0 : (((α : ℂ) - T * I)).re ≤ (((2 : ℂ) + T * I)).re := by simpa using hα
  have hi0 : (((α : ℂ) - T * I)).im ≤ (((2 : ℂ) + T * I)).im := by
    simpa using (show -T ≤ T by linarith)
  have hsR : α ≤ s.re ∧ s.re ≤ 2 ∧ -T ≤ s.im ∧ s.im ≤ T := by
    simpa using (mem_Rect hr0 hi0 s).mp hs0.1
  refine ⟨(mem_Rect hre him s).mpr ?_, hs0.2.1, hs0.2.2, ?_⟩
  · simpa using (show a ≤ s.re ∧ s.re ≤ 2 ∧ -U ≤ s.im ∧ s.im ≤ U from
      ⟨by linarith [ha.2], hsR.2.1, by linarith [hU.1, hsR.2.2.1],
        by linarith [hU.1, hsR.2.2.2]⟩)
  · simpa using (show a + d ≤ s.re by linarith [ha.2, hsR.1])

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
