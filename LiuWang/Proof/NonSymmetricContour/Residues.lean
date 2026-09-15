import LiuWang.Proof.NonSymmetricContour.Kernel
import LiuWang.Proof.NonSymmetricContour.ZeroIndex
import LiuWang.Proof.NonSymmetricContour.Rectangle
import BombieriVinogradov.Helpers.ComplexAnalysis.RectanglePoles
import BombieriVinogradov.Helpers.ComplexAnalysis.SumResiduesFinset

/-! # 非对称矩形内全部实际留数，包含普通 L 函数原点零阶 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

namespace LiuWang.Proof.NonSymmetricContour

theorem rectangle_residue_identity {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t b Hplus Hminus : Real} (ht : 0 < t) (hb : 1 ≤ b)
    (hp : 0 < Hplus) (hm : Hminus < 0)
    (hborder : ∀ s ∈ RectangleBorder (lowerLeft Hminus) (upperRight b Hplus),
      chi.LFunction s ≠ 0) :
    RectangleIntegral' (horizontalIntegrand chi t)
        (lowerLeft Hminus) (upperRight b Hplus) =
      -(∑ p ∈ rectangleZeroIndices chi Hplus Hminus,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p) -
        (lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex) := by
  classical
  let G := analyticIntegrand chi t
  let R := Complex.Rectangle (lowerLeft Hminus) (upperRight b Hplus)
  let V := insert (0 : Complex) (rectangleZeroValues chi Hplus Hminus)
  let P := {s : Complex | meromorphicOrderAt G s < 0}
  have hH : Hminus ≤ Hplus := by linarith
  have hzero := zero_not_mem_border hb hp hm
  have hmero : Meromorphic G := meromorphic_analyticIntegrand hchi ht
  have hdisj : Disjoint (RectangleBorder (lowerLeft Hminus) (upperRight b Hplus)) P := by
    rw [Set.disjoint_left]
    intro s hs hsp
    exact not_lt_of_ge (analyticAt_analyticIntegrand hchi ht
      (hborder s hs)).meromorphicOrderAt_nonneg hsp
  have hVinR : (V : Set Complex) ⊆ R := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact (mem_rectangle hb hH 0).mpr
        ⟨⟨by norm_num, by simpa using (show (0 : Real) ≤ b by linarith)⟩, hm.le, hp.le⟩
    · obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hs
      have hr := completedZeroValue_re_mem_Ioo hchi hPrimitive p
      have hi := (mem_rectangleZeroIndices hchi hPrimitive Hplus Hminus p).mp hpS
      exact (mem_rectangle hb hH _).mpr ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩,
        hi.1.le, hi.2.le⟩
  have hset : R ∩ P = (V : Set Complex) ∩ P := by
    ext s
    constructor
    · rintro ⟨hsR, hsP⟩
      refine ⟨?_, hsP⟩
      by_cases hs0 : s = 0
      · exact Finset.mem_insert.mpr (Or.inl hs0)
      have hz : chi.LFunction s = 0 := by
        by_contra hn
        exact not_lt_of_ge (analyticAt_analyticIntegrand hchi ht hn).meromorphicOrderAt_nonneg hsP
      have hs := (mem_rectangle hb hH s).mp hsR
      have hre : 0 < s.re := re_pos_of_LFunction_eq_zero_of_neg_one_lt_re
        hchi hPrimitive (by linarith [hs.1.1]) hs0 hz
      obtain ⟨p, hpv⟩ := LocalAnalyticBounds.exists_completedZeroIndex_value_eq_of_LFunction_zero
        hchi hPrimitive hre hz
      have hbottom : Hminus < s.im := by
        apply lt_of_le_of_ne hs.2.1
        intro heq
        exact hborder s ((mem_border hb hH s).mpr (Or.inl (Or.inl ⟨hs.1, heq.symm⟩))) hz
      have htop : s.im < Hplus := by
        apply lt_of_le_of_ne hs.2.2
        intro heq
        exact hborder s ((mem_border hb hH s).mpr (Or.inr (Or.inl ⟨hs.1, heq⟩))) hz
      apply Finset.mem_insert.mpr ∘ Or.inr
      apply Finset.mem_image.mpr
      exact ⟨p, (mem_rectangleZeroIndices hchi hPrimitive Hplus Hminus p).mpr
        (by simpa [hpv] using And.intro hbottom htop), hpv⟩
    · exact fun hs => ⟨hVinR hs.1, hs.2⟩
  have hrect : RectangleIntegral' G (lowerLeft Hminus) (upperRight b Hplus) =
      sumResiduesIn G (V : Set Complex) := by
    rw [RectangleIntegral'_eq_sumResiduesIn (by simp; linarith) (by simpa using hH)
      hmero.meromorphicOn hdisj
      (BombieriVinogradov.ComplexAnalysis.finite_polesIn_rectangle G _ _ hmero.meromorphicOn)
      (simple_analyticIntegrand hchi ht _)]
    exact sumResiduesIn_inter_eq_of_set_eq hset (fun s _ hs =>
      residue_eq_zero_of_not_pole_of_meromorphicAt (hmero s) (le_of_not_gt hs))
  have hsum :
      ∑ rho ∈ rectangleZeroValues chi Hplus Hminus, residue G rho =
        -(∑ p ∈ rectangleZeroIndices chi Hplus Hminus, centeredKernel t (completedZeroValue p)) := by
    calc
      _ = -(∑ rho ∈ rectangleZeroValues chi Hplus Hminus,
          (analyticOrderNatAt chi.LFunction rho : Complex) * centeredKernel t rho) := by
        simp [G, residue_analyticIntegrand hchi ht]
      _ = _ := by rw [sum_rectangleZeroValues_multiplicity hchi hPrimitive]
  have hsumK :
      ∑ p ∈ rectangleZeroIndices chi Hplus Hminus, centeredKernel t (completedZeroValue p) =
      ∑ p ∈ rectangleZeroIndices chi Hplus Hminus,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p := by
    apply Finset.sum_congr rfl
    intro p _
    apply centeredKernel_eq
    intro hz
    have hr := (completedZeroValue_re_mem_Ioo hchi hPrimitive p).1
    simp [hz] at hr
  calc
    _ = RectangleIntegral' G (lowerLeft Hminus) (upperRight b Hplus) := by
      apply RectangleIntegral'_congr
      intro s hs
      exact (analyticIntegrand_eq chi t (fun hz => hzero (hz ▸ hs))).symm
    _ = sumResiduesIn G (V : Set Complex) := hrect
    _ = ∑ s ∈ V, residue G s := BombieriVinogradov.ComplexAnalysis.sumResiduesIn_finset _ _
    _ = _ := by
      rw [Finset.sum_insert (zero_not_mem_rectangleZeroValues hchi hPrimitive Hplus Hminus),
        hsum, hsumK]
      change residue (analyticIntegrand chi t) 0 + _ = _
      rw [residue_analyticIntegrand_zero hchi ht]
      ring

theorem right_integral_add_zeros_add_origin_eq_threeSides
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t b Hplus Hminus : Real} (ht : 0 < t) (hb : 1 ≤ b)
    (hp : 0 < Hplus) (hm : Hminus < 0)
    (hborder : ∀ s ∈ RectangleBorder (lowerLeft Hminus) (upperRight b Hplus),
      chi.LFunction s ≠ 0) :
    verticalIntegral (horizontalIntegrand chi t) b Hplus Hminus +
      (∑ p ∈ rectangleZeroIndices chi Hplus Hminus,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p) +
      (lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex) =
        threeSides (horizontalIntegrand chi t) b Hplus Hminus := by
  rw [rectangle_orientation, rectangle_residue_identity hchi hPrimitive ht hb hp hm hborder]
  ring

end LiuWang.Proof.NonSymmetricContour
