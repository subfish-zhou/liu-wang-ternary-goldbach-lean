import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HRectangle

/-! A detector-local closed-rectangle zeta count, with actual finite analytic multiplicities. -/

set_option autoImplicit false

noncomputable section

open Complex Set

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem zeta_rectangle_zeros_finite (z w : ℂ) :
    {s ∈ Rectangle z w | s ≠ 1 ∧ riemannZeta s = 0}.Finite := by
  have h := divisor_support_rectangle_finite (entireH 4) z w
  rw [entireH_divisor_support (by norm_num : (3 : ℝ) < 4)] at h
  apply h.subset
  intro s hs
  refine ⟨hs.1, ?_⟩
  rw [entireH_eq hs.2.1, H_factorization, hs.2.2]
  simp

def zetaDetectorRectangleCount (z w : ℂ) : ℕ :=
  ∑ s ∈ (zeta_rectangle_zeros_finite z w).toFinset, analyticOrderNatAt riemannZeta s

theorem zetaDetectorRectangleCount_actual_orders (z w : ℂ) :
    (zetaDetectorRectangleCount z w : ℕ∞) =
      ∑ s ∈ (zeta_rectangle_zeros_finite z w).toFinset, analyticOrderAt riemannZeta s := by
  simp only [zetaDetectorRectangleCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs1 := ((zeta_rectangle_zeros_finite z w).mem_toFinset.mp hs).2.1
  exact Nat.cast_analyticOrderNatAt (zeta_order_finite (by norm_num : (3 : ℝ) < 4) hs1)

theorem zetaDetectorRectangleCount_le {y : ℝ} (hy : 3 < y) (z w : ℂ) :
    zetaDetectorRectangleCount z w ≤ detectorCount y z w := by
  apply zeta_finite_sum_le_detectorCount hy
  intro s hs
  have hm := (zeta_rectangle_zeros_finite z w).mem_toFinset.mp hs
  exact ⟨hm.1, hm.2.1⟩

theorem closed_zeta_count_detected {y a T ε : ℝ} (hy : 3 < y)
    (ha : a ≤ 2) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ a' ∈ Ioo (a - ε) a, ∃ T' ∈ Ioo T (T + ε),
      (∀ s ∈ RectangleBorder ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I),
        entireH y s ≠ 0) ∧
      RectangleBorderIntegrable (logDeriv (entireH y))
        ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) ∧
      RectangleIntegral' (logDeriv (entireH y))
        ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) =
        (detectorCount y ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) : ℂ) ∧
      zetaDetectorRectangleCount ((a : ℂ) - T * I) ((2 : ℂ) + T * I) ≤
        detectorCount y ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) := by
  obtain ⟨a', ha', T', hT', hb, hi, hc, hS⟩ := actual_perturbed_detector_count hy ha hT hε
  refine ⟨a', ha', T', hT', hb, hi, hc, hS _ ?_⟩
  intro s hs
  have hm := (zeta_rectangle_zeros_finite ((a : ℂ) - T * I)
    ((2 : ℂ) + T * I)).mem_toFinset.mp hs
  have hre : (((a : ℂ) - T * I)).re ≤ (((2 : ℂ) + T * I)).re := by simpa using ha
  have him : (((a : ℂ) - T * I)).im ≤ (((2 : ℂ) + T * I)).im := by
    simpa using (show -T ≤ T by linarith)
  have hmem := (mem_Rect hre him s).mp hm.1
  have hr : a ≤ s.re ∧ s.re ≤ 2 ∧ -T ≤ s.im ∧ s.im ≤ T := by simpa using hmem
  exact ⟨hr.1, hr.2.1, abs_le.mpr hr.2.2, hm.2.1⟩

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
