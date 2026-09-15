import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HMultiplicity
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Legal zero-free perturbations and an actual rectangular detector argument principle. -/

set_option autoImplicit false

noncomputable section

open Complex Set

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem entireH_zeros_countable {y : ℝ} (hy : 3 < y) :
    {s : ℂ | entireH y s = 0}.Countable := by
  have h := MeromorphicOn.divisor_support_countable (entireH y) univ
  rw [entireH_divisor_support hy] at h
  simpa using h

theorem entireH_two_line_ne_zero {y : ℝ} (hy : 3 < y) {s : ℂ} (hs : s.re = 2) :
    entireH y s ≠ 0 := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [entireH_eq hs1]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hs1)) (H_ne_zero_on_two hs hy)

theorem entireH_boundary_perturbation {y a T ε : ℝ} (hy : 3 < y) (hε : 0 < ε) :
    ∃ a' ∈ Ioo (a - ε) a, ∃ T' ∈ Ioo T (T + ε),
      ∀ s ∈ RectangleBorder ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I),
        entireH y s ≠ 0 := by
  let Z : Set ℂ := {s | entireH y s = 0}
  have hZ : Z.Countable := entireH_zeros_countable hy
  obtain ⟨a', ha', ha⟩ := ((hZ.image Complex.re).dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (by linarith : a - ε < a))
  have hbad := (hZ.image Complex.im).union (hZ.image (fun s : ℂ => -s.im))
  obtain ⟨T', hT', hT⟩ := (hbad.dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (by linarith : T < T + ε))
  refine ⟨a', ha, T', hT, ?_⟩
  intro s hs hz
  have hr : s.re ≠ a' := by
    intro h
    exact ha' ⟨s, hz, h⟩
  have hi : s.im ≠ T' := by
    intro h
    exact hT' (Or.inl ⟨s, hz, h⟩)
  have hn : s.im ≠ -T' := by
    intro h
    exact hT' (Or.inr ⟨s, hz, by linarith⟩)
  have htwo : s.re ≠ 2 := fun h => entireH_two_line_ne_zero hy h hz
  simp [RectangleBorder] at hs
  rcases hs with ((hs | hs) | hs) | hs
  · exact hn hs.2
  · exact hr hs.1
  · exact hi hs.2
  · exact htwo hs.1

theorem entireH_logDeriv_boundary_integrable {y : ℝ} {z w : ℂ}
    (hb : ∀ s ∈ RectangleBorder z w, entireH y s ≠ 0) :
    RectangleBorderIntegrable (logDeriv (entireH y)) z w := by
  apply ContinuousOn.rectangleBorder_integrable
  intro s hs
  exact ((differentiable_entireH y).analyticAt s |>.deriv.continuousAt.div
    ((differentiable_entireH y).continuous.continuousAt) (hb s hs)).continuousWithinAt

theorem entireH_rectangle_count {y : ℝ} (hy : 3 < y) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, entireH y s ≠ 0) :
    RectangleIntegral' (logDeriv (entireH y)) z w = (detectorCount y z w : ℂ) := by
  have hm : MeromorphicOn (entireH y) (Rectangle z w) :=
    fun s _ => (analytic_entireH y s).meromorphicAt
  have hf : ∀ s ∈ Rectangle z w, meromorphicOrderAt (entireH y) s ≠ ⊤ := by
    intro s _
    rw [(analytic_entireH y s).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (entireH_order_finite hy s)]
    simp
  have hd : Disjoint (RectangleBorder z w)
      (MeromorphicOn.divisor (entireH y) (Rectangle z w)).support := by
    rw [entireH_divisor_support hy, Set.disjoint_left]
    exact fun s hs hz => hb s hs hz.2
  rw [rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt hre him hm hm.logDeriv hf hd]
  exact (detectorCount_divisor hy z w).symm

theorem actual_perturbed_detector_count {y a T ε : ℝ} (hy : 3 < y)
    (ha : a ≤ 2) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ a' ∈ Ioo (a - ε) a, ∃ T' ∈ Ioo T (T + ε),
      (∀ s ∈ RectangleBorder ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I),
        entireH y s ≠ 0) ∧
      RectangleBorderIntegrable (logDeriv (entireH y))
        ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) ∧
      RectangleIntegral' (logDeriv (entireH y))
        ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) =
        (detectorCount y ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) : ℂ) ∧
      ∀ S : Finset ℂ, (∀ s ∈ S, a ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ T ∧ s ≠ 1) →
        (∑ s ∈ S, analyticOrderNatAt riemannZeta s) ≤
          detectorCount y ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I) := by
  obtain ⟨a', ha', T', hT', hb⟩ := entireH_boundary_perturbation hy hε (a := a) (T := T)
  have hre : (((a' : ℂ) - T' * I)).re ≤ (((2 : ℂ) + T' * I)).re := by
    simpa using (show a' ≤ 2 by linarith [ha'.2])
  have him : (((a' : ℂ) - T' * I)).im ≤ (((2 : ℂ) + T' * I)).im := by
    simpa using (show -T' ≤ T' by linarith [hT'.1])
  refine ⟨a', ha', T', hT', hb, entireH_logDeriv_boundary_integrable hb,
    entireH_rectangle_count hy hre him hb, ?_⟩
  intro S hS
  apply zeta_finite_sum_le_detectorCount hy S
  intro s hs
  obtain ⟨hs0, hs2, hst, hs1⟩ := hS s hs
  refine ⟨(mem_Rect hre him s).mpr ?_, hs1⟩
  have hab := abs_le.mp hst
  simpa using (show a' ≤ s.re ∧ s.re ≤ 2 ∧ -T' ≤ s.im ∧ s.im ≤ T' from
    ⟨by linarith [ha'.2], hs2, by linarith [hT'.1], by linarith [hT'.1]⟩)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
