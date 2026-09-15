import LiuWang.Proof.SourceRoute.Density.WeightedContour
import LiuWang.Proof.SourceRoute.Density.FamilyBoundary

/-! Closed-height ordinary L multiplicities are paid by the same weighted H contour. -/

set_option autoImplicit false

noncomputable section

open Complex Set
open LiuWang.Proof.Interfaces (Character zeroMultiplicity)
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density

def weightedContour (q : ℕ) [NeZero q] (X a U : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q,
    (RectangleIntegral' (weightedKernel (H chi X) ((a : ℂ) - U * I))
      ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re) / q.totient

theorem weighted_L_sum_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X d : ℝ} (hX : 3 < X) (hd : 0 ≤ d) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, H chi X s ≠ 0)
    (S : Finset ℂ) (hS : ∀ s ∈ S,
      s ∈ Rectangle z w ∧ chi.LFunction s = 0 ∧ z.re + d ≤ s.re) :
    d * (∑ s ∈ S, zeroMultiplicity chi s : ℕ) ≤
      (RectangleIntegral' (weightedKernel (H chi X) z) z w).re := by
  classical
  let D := (divisor_support_rectangle_finite (H chi X) z w).toFinset
  have hsub : S ⊆ D := by
    intro s hs
    apply (divisor_support_rectangle_finite (H chi X) z w).mem_toFinset.mpr
    rw [H_divisor_support hchi hX]
    exact ⟨(hS s hs).1, H_eq_zero_of_LFunction_eq_zero (hS s hs).2.1 X⟩
  rw [weighted_rectangle_re (differentiable_H hchi X)
    (analyticOrder_H_ne_top hchi hX) hre him hb]
  simp only [Nat.cast_sum, Finset.mul_sum]
  apply le_trans (b := ∑ s ∈ S,
    (s.re - z.re) * (analyticOrderNatAt (H chi X) s : ℝ))
  · apply Finset.sum_le_sum
    intro s hs
    have hm : (zeroMultiplicity chi s : ℝ) ≤
        (analyticOrderNatAt (H chi X) s : ℝ) :=
      Nat.cast_le.mpr (multiplicity_le_detector hchi hX s)
    exact mul_le_mul (by linarith [(hS s hs).2.2]) hm (by positivity)
      (by linarith [(hS s hs).2.2])
  · apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro s hs _
    have hsR := (MeromorphicOn.divisor (H chi X) (Rectangle z w)).supportWithinDomain
      ((divisor_support_rectangle_finite (H chi X) z w).mem_toFinset.mp hs)
    exact mul_nonneg (sub_nonneg.mpr ((mem_Rect hre him s).mp hsR).1) (Nat.cast_nonneg _)

theorem closed_count_weighted_le (q : ℕ) [NeZero q] {X alpha T a U d : ℝ}
    (hX : 3 < X) (ha : a ≤ 2) (hU : 0 ≤ U) (hTU : T ≤ U)
    (hd : 0 ≤ d) (hgap : a + d ≤ alpha)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    d * ((nonprincipalCount q alpha T : ℝ) / q.totient) ≤ weightedContour q X a U := by
  have hre : (((a : ℂ) - U * I)).re ≤ (((2 : ℂ) + U * I)).re := by simpa using ha
  have him : (((a : ℂ) - U * I)).im ≤ (((2 : ℂ) + U * I)).im := by
    simpa using (show -U ≤ U by linarith)
  rw [weightedContour, nonprincipalCount_eq_multiplicity_sum]
  simp only [Nat.cast_sum, ← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro chi hchi
  rw [← Finset.mul_sum, ← Nat.cast_sum]
  apply weighted_L_sum_le ((mem_nonprincipalCharacters chi).mp hchi) hX hd hre him
    (hb chi hchi)
  intro s hs
  obtain ⟨hz, ⟨_, hs1, hst⟩, hsa⟩ := DirichletZeroCount.mem_zeroValues.mp hs
  have ht := abs_le.mp hst
  refine ⟨(mem_Rect hre him s).mpr ?_, hz, ?_⟩
  · simpa using (show a ≤ s.re ∧ s.re ≤ 2 ∧ -U ≤ s.im ∧ s.im ≤ U from
      ⟨by linarith, by linarith, by linarith, by linarith⟩)
  · simpa using (show a + d ≤ s.re by linarith)

theorem produced_closed_weighted_count (q : ℕ) [NeZero q] {X alpha T d e : ℝ}
    (hX : 3 < X) (halpha : alpha ≤ 2) (hT : 0 ≤ T) (hd : 0 < d) (he : 0 < e) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) ∧
      (∀ chi ∈ nonprincipalCharacters q,
        RectangleBorderIntegrable (weightedKernel (H chi X) ((a : ℂ) - U * I))
          ((a : ℂ) - U * I) ((2 : ℂ) + U * I)) ∧
      d * ((nonprincipalCount q alpha T : ℝ) / q.totient) ≤ weightedContour q X a U := by
  obtain ⟨a, ha, U, hU, hb⟩ :=
    family_boundary_perturbation q hX he (a := alpha - d) (T := T)
  refine ⟨a, ha, U, hU, hb, ?_, ?_⟩
  · exact fun chi hchi => weighted_integrable
      (differentiable_H ((mem_nonprincipalCharacters chi).mp hchi) X) (hb chi hchi)
  · exact closed_count_weighted_le q hX (by linarith [ha.2]) (by linarith [hU.1])
      hU.1.le hd.le (by linarith [ha.2]) hb

@[simp] theorem weightedContour_one (X a U : ℝ) : weightedContour 1 X a U = 0 := by
  simp [weightedContour]

@[simp] theorem weightedContour_two (X a U : ℝ) : weightedContour 2 X a U = 0 := by
  simp [weightedContour]

end LiuWang.Proof.SourceRoute.Density
