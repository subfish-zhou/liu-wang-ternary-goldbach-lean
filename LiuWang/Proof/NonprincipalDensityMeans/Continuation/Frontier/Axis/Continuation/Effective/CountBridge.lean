import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.Effective.Contour

/-! Closed ordinary-L multiplicities transported to the same produced H rectangle.
This is the unweighted argument principle, not the still-unpaid weighted density inequality.
-/

set_option autoImplicit false
noncomputable section

open Complex Set Finset
open LiuWang.Proof.Interfaces (Character zeroMultiplicity)
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective

theorem H_divisor_value {q : ℕ} [NeZero q] {chi : Character q} (hchi : chi ≠ 1)
    {X : ℝ} (hX : 3 < X) {U : Set ℂ} {s : ℂ} (hs : s ∈ U) :
    MeromorphicOn.divisor (H chi X) U s = (analyticOrderNatAt (H chi X) s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => (differentiable_H hchi X).analyticAt z) hs,
    ← Nat.cast_analyticOrderNatAt (analyticOrder_H_ne_top hchi hX s)]
  simp

theorem H_divisor_support {q : ℕ} [NeZero q] {chi : Character q} (hchi : chi ≠ 1)
    {X : ℝ} (hX : 3 < X) (U : Set ℂ) :
    (MeromorphicOn.divisor (H chi X) U).support = {s ∈ U | H chi X s = 0} := by
  ext s
  by_cases hs : s ∈ U
  · rw [Function.mem_support, H_divisor_value hchi hX hs]
    have ho := ((differentiable_H hchi X).analyticAt s).analyticOrderAt_eq_zero
    rw [← Nat.cast_analyticOrderNatAt (analyticOrder_H_ne_top hchi hX s)] at ho
    simp only [Nat.cast_eq_zero] at ho ⊢
    simp only [mem_ofPred_eq, hs, true_and]
    have hn : analyticOrderNatAt (H chi X) s ≠ 0 ↔ H chi X s = 0 := by tauto
    exact_mod_cast hn
  · have hn : s ∉ (MeromorphicOn.divisor (H chi X) U).support :=
      fun h => hs ((MeromorphicOn.divisor (H chi X) U).supportWithinDomain h)
    simp [hn, hs]

def HRectangleCount (q : ℕ) [NeZero q] (X : ℝ) (z w : ℂ) : ℕ :=
  ∑ chi ∈ nonprincipalCharacters q,
    ∑ s ∈ (divisor_support_rectangle_finite (H chi X) z w).toFinset,
      analyticOrderNatAt (H chi X) s

theorem nonprincipalCount_le_HRectangleCount (q : ℕ) [NeZero q] {X alpha y a u : ℝ}
    (hX : 3 < X) (ha : a ≤ alpha) (ha2 : a ≤ 2) (hy : 0 ≤ y) (hyu : y ≤ u) :
    nonprincipalCount q alpha y ≤ HRectangleCount q X ((a : ℂ) - u * I) ((2 : ℂ) + u * I) := by
  apply (nonprincipalCount_le_detector_orders q alpha y hX).trans
  apply sum_le_sum
  intro chi hchi
  have hc := (mem_nonprincipalCharacters chi).mp hchi
  apply sum_le_sum_of_subset_of_nonneg
  · intro s hs
    rw [Set.Finite.mem_toFinset, H_divisor_support hc hX]
    obtain ⟨hz, ⟨_, h1, ht⟩, halpha⟩ := DirichletZeroCount.mem_zeroValues.mp hs
    refine ⟨?_, H_eq_zero_of_LFunction_eq_zero hz X⟩
    have hre : (((a : ℂ) - u * I)).re ≤ (((2 : ℂ) + u * I)).re := by simpa using ha2
    have him : (((a : ℂ) - u * I)).im ≤ (((2 : ℂ) + u * I)).im := by
      simpa using (show -u ≤ u by linarith)
    apply (mem_Rect hre him s).mpr
    have ht' := abs_le.mp ht
    simpa using (show a ≤ s.re ∧ s.re ≤ 2 ∧ -u ≤ s.im ∧ s.im ≤ u from
      ⟨ha.trans halpha, by linarith, by linarith [ht'.1], by linarith [ht'.2]⟩)
  · intro s _ _
    exact Nat.zero_le _

theorem H_rectangle_argument_principle {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 3 < X) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, H chi X s ≠ 0) :
    RectangleIntegral' (logDeriv (H chi X)) z w =
      ∑ s ∈ (divisor_support_rectangle_finite (H chi X) z w).toFinset,
        (analyticOrderNatAt (H chi X) s : ℂ) := by
  have hm : MeromorphicOn (H chi X) (Rectangle z w) :=
    fun s _ => ((differentiable_H hchi X).analyticAt s).meromorphicAt
  have hf : ∀ s ∈ Rectangle z w, meromorphicOrderAt (H chi X) s ≠ ⊤ := by
    intro s _
    rw [((differentiable_H hchi X).analyticAt s).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (analyticOrder_H_ne_top hchi hX s)]
    simp
  have hd : Disjoint (RectangleBorder z w) (MeromorphicOn.divisor (H chi X) (Rectangle z w)).support := by
    rw [H_divisor_support hchi hX, Set.disjoint_left]
    exact fun s hs hz => hb s hs hz.2
  rw [rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt hre him hm hm.logDeriv hf hd]
  apply sum_congr rfl
  intro s hs
  rw [H_divisor_value hchi hX
    ((MeromorphicOn.divisor (H chi X) (Rectangle z w)).supportWithinDomain
      ((divisor_support_rectangle_finite (H chi X) z w).mem_toFinset.mp hs))]
  simp

theorem HRectangleCount_eq_contour_sum (q : ℕ) [NeZero q] {X : ℝ} (hX : 3 < X)
    {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ chi ∈ nonprincipalCharacters q, ∀ s ∈ RectangleBorder z w, H chi X s ≠ 0) :
    (HRectangleCount q X z w : ℝ) =
      ∑ chi ∈ nonprincipalCharacters q, (RectangleIntegral' (logDeriv (H chi X)) z w).re := by
  unfold HRectangleCount
  simp only [Nat.cast_sum]
  apply sum_congr rfl
  intro chi hchi
  rw [H_rectangle_argument_principle ((mem_nonprincipalCharacters chi).mp hchi) hX hre him (hb chi hchi),
    Complex.re_sum]
  simp

theorem produced_closed_count_and_effective_contour (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y sigma alpha eps : ℝ} (hy : 2 ≤ y) (hqy : (q : ℝ) ≤ y)
    (hs : sigma ≤ 1) (hsa : sigma ≤ alpha) (heps : 0 < eps) (ha : 3 / 4 ≤ sigma - eps) :
    ∃ a ∈ Ioo (sigma - eps) sigma, ∃ u ∈ Ioo y (y + eps),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - u * I) ((2 : ℂ) + u * I), H chi ((q : ℝ) * y) s ≠ 0) ∧
      (nonprincipalCount q alpha y : ℝ) / q.totient ≤
        (∑ chi ∈ nonprincipalCharacters q,
          (RectangleIntegral' (logDeriv (H chi ((q : ℝ) * y))) ((a : ℂ) - u * I) ((2 : ℂ) + u * I)).re) /
            q.totient ∧
      2 * Real.pi * weightedContour q ((q : ℝ) * y) a u ≤
        4563648 * balancedPower q y (sigma - eps) * (1 + Real.log ((q : ℝ) * y)) ^ 5 +
          horizontalDifference q ((q : ℝ) * y) a u := by
  obtain ⟨a, ha', u, hu', hb, hv⟩ := produced_family_littlewood_effective q hq hy hqy hs heps ha
  refine ⟨a, ha', u, hu', hb, ?_, hv⟩
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hX : 3 < (q : ℝ) * y := by nlinarith
  have ha2 : a ≤ 2 := by linarith [ha'.2]
  have hre : (((a : ℂ) - u * I)).re ≤ (((2 : ℂ) + u * I)).re := by simpa using ha2
  have him : (((a : ℂ) - u * I)).im ≤ (((2 : ℂ) + u * I)).im := by
    simpa using (show -u ≤ u by linarith [hu'.1])
  have h := Nat.cast_le (α := ℝ) |>.mpr
    (nonprincipalCount_le_HRectangleCount q hX (by linarith [ha'.2] : a ≤ alpha)
      ha2 (by linarith : 0 ≤ y) hu'.1.le)
  rw [HRectangleCount_eq_contour_sum q hX hre him hb] at h
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective
