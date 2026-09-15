import LiuWang.Proof.NonprincipalDensityAdvance.Family
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HRectangle

/-! One zero-free rectangle for all nonprincipal characters at the fixed cutoff X. -/

set_option autoImplicit false

noncomputable section

open Complex Set
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density

theorem H_divisor_apply {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 3 < X) {U : Set ℂ} {s : ℂ} (hs : s ∈ U) :
    MeromorphicOn.divisor (H chi X) U s = (analyticOrderNatAt (H chi X) s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => (differentiable_H hchi X).analyticAt z) hs,
    ← Nat.cast_analyticOrderNatAt (analyticOrder_H_ne_top hchi hX s)]
  simp

theorem H_divisor_support {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 3 < X) (U : Set ℂ) :
    (MeromorphicOn.divisor (H chi X) U).support = {s ∈ U | H chi X s = 0} := by
  ext s
  by_cases hs : s ∈ U
  · rw [Function.mem_support, H_divisor_apply hchi hX hs]
    have ho := ((differentiable_H hchi X).analyticAt s).analyticOrderAt_eq_zero
    rw [← Nat.cast_analyticOrderNatAt (analyticOrder_H_ne_top hchi hX s)] at ho
    simp only [Nat.cast_eq_zero] at ho
    simp only [mem_ofPred_eq, hs, true_and]
    have hn : analyticOrderNatAt (H chi X) s ≠ 0 ↔ H chi X s = 0 := by tauto
    exact_mod_cast hn
  · have hnot : s ∉ (MeromorphicOn.divisor (H chi X) U).support :=
      fun h => hs ((MeromorphicOn.divisor (H chi X) U).supportWithinDomain h)
    simp [hnot, hs]

theorem H_zeros_countable {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 3 < X) :
    {s : ℂ | H chi X s = 0}.Countable := by
  have h := MeromorphicOn.divisor_support_countable (H chi X) univ
  rw [H_divisor_support hchi hX] at h
  simpa using h

theorem family_boundary_perturbation (q : ℕ) [NeZero q] {X a T e : ℝ}
    (hX : 3 < X) (he : 0 < e) :
    ∃ a' ∈ Ioo (a - e) a, ∃ U ∈ Ioo T (T + e),
      ∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a' : ℂ) - U * I) ((2 : ℂ) + U * I),
          H chi X s ≠ 0 := by
  let Z : Set ℂ := ⋃ chi : {chi // chi ∈ nonprincipalCharacters q},
    {s | H chi.val X s = 0}
  have hZ : Z.Countable := Set.countable_iUnion fun chi =>
    H_zeros_countable ((mem_nonprincipalCharacters chi.val).mp chi.property) hX
  obtain ⟨a', ha', ha⟩ := ((hZ.image Complex.re).dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (by linarith : a - e < a))
  have hbad := (hZ.image Complex.im).union (hZ.image (fun s : ℂ => -s.im))
  obtain ⟨U, hU', hU⟩ := (hbad.dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (by linarith : T < T + e))
  refine ⟨a', ha, U, hU, ?_⟩
  intro chi hchi s hs hz
  have hsZ : s ∈ Z := mem_iUnion.mpr ⟨⟨chi, hchi⟩, hz⟩
  have hr : s.re ≠ a' := fun h => ha' ⟨s, hsZ, h⟩
  have hi : s.im ≠ U := fun h => hU' (Or.inl ⟨s, hsZ, h⟩)
  have hn : s.im ≠ -U := by
    intro h
    exact hU' (Or.inr ⟨s, hsZ, by linarith⟩)
  have htwo : s.re ≠ 2 := fun h => H_ne_zero_on_two chi h hX hz
  simp [RectangleBorder] at hs
  rcases hs with ((hs | hs) | hs) | hs
  · exact hn hs.2
  · exact hr hs.1
  · exact hi hs.2
  · exact htwo hs.1

end LiuWang.Proof.SourceRoute.Density
