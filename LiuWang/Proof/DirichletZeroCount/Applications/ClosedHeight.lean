import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

/-!
# Common regular heights preserving the actual closed-window counts

The finite envelope is produced by the ordinary-L zero sets, not assumed.
One height works for every character and every alpha, retaining zeros exactly
at the original height and on the critical line.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount.Applications

theorem finite_height_clearance (F : Finset ℂ) (y : ℝ) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ rho ∈ F, y < |rho.im| → y + e < |rho.im| := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert rho F hnot ih =>
    obtain ⟨e, he, he1, hgap⟩ := ih
    by_cases hrho : y < |rho.im|
    · refine ⟨min e ((|rho.im| - y) / 2), lt_min he (by linarith),
        (min_le_left _ _).trans he1, ?_⟩
      intro z hz hzheight
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have h := min_le_right e ((|z.im| - y) / 2)
        linarith
      · have hg := hgap z hz hzheight
        have hm := min_le_left e ((|rho.im| - y) / 2)
        linarith
    · refine ⟨e, he, he1, ?_⟩
      intro z hz hzheight
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (hrho hzheight).elim
      · exact hgap z hz hzheight

theorem exists_common_regular_height (q : ℕ) [NeZero q] {y r : ℝ}
    (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧
      (∀ chi : Character q, ∀ alpha t : ℝ, y ≤ t → t ≤ H →
        zeroValues chi alpha t = zeroValues chi alpha y) ∧
      (∀ chi : Character q, ∀ rho : ℂ, 0 < rho.re → rho.re < 1 →
        |rho.im| = H → chi.LFunction rho ≠ 0) := by
  let F := (Finset.univ : Finset (Character q)).biUnion
    (fun chi => zeroValues chi 0 (y + 1))
  obtain ⟨e, he, he1, hgap⟩ := finite_height_clearance F y
  let d := min e (r / 2)
  have hd : 0 < d := lt_min he (by linarith)
  have hde : d ≤ e := min_le_left _ _
  have hdr : d ≤ r / 2 := min_le_right _ _
  have hH1 : y + d ≤ y + 1 := by linarith
  have hmem (chi : Character q) (rho : ℂ) (hz : chi.LFunction rho = 0)
      (h0 : 0 < rho.re) (h1 : rho.re < 1) (ht : |rho.im| ≤ y + 1) : rho ∈ F :=
    Finset.mem_biUnion.mpr ⟨chi, Finset.mem_univ _,
      mem_zeroValues.mpr ⟨hz, ⟨h0, h1, ht⟩, h0.le⟩⟩
  refine ⟨y + d, by linarith, by linarith, ?_, ?_⟩
  · intro chi alpha t hyt htH
    ext rho
    constructor
    · intro hrho
      obtain ⟨hz, ⟨h0, h1, ht⟩, ha⟩ := mem_zeroValues.mp hrho
      have hheight : |rho.im| ≤ y := by
        by_contra h
        have hstrict := hgap rho (hmem chi rho hz h0 h1 (ht.trans (htH.trans hH1)))
          (lt_of_not_ge h)
        linarith
      exact mem_zeroValues.mpr ⟨hz, ⟨h0, h1, hheight⟩, ha⟩
    · intro hrho
      obtain ⟨hz, ⟨h0, h1, ht⟩, ha⟩ := mem_zeroValues.mp hrho
      exact mem_zeroValues.mpr ⟨hz, ⟨h0, h1, ht.trans hyt⟩, ha⟩
  · intro chi rho h0 h1 ht hz
    have hstrict := hgap rho (hmem chi rho hz h0 h1 (ht.le.trans hH1))
      (by linarith : y < |rho.im|)
    linarith

theorem exists_common_count_plateau (q : ℕ) [NeZero q] {y r : ℝ}
    (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧
      (∀ chi : Character q, ∀ alpha t : ℝ, y ≤ t → t ≤ H →
        count chi alpha t = count chi alpha y) ∧
      (∀ alpha t : ℝ, y ≤ t → t ≤ H → familyCount q alpha t = familyCount q alpha y) ∧
      (∀ chi : Character q, ∀ rho : ℂ, 0 < rho.re → rho.re < 1 →
        |rho.im| = H → chi.LFunction rho ≠ 0) := by
  obtain ⟨H, hyH, hHr, hvalues, hreg⟩ := exists_common_regular_height q hr
  have hc (chi : Character q) (alpha t : ℝ) (hyt : y ≤ t) (htH : t ≤ H) :
      count chi alpha t = count chi alpha y := by
    rw [count, hvalues chi alpha t hyt htH, count]
  refine ⟨H, hyH, hHr, hc, ?_, hreg⟩
  intro alpha t hyt htH
  simp only [familyCount, hc _ alpha t hyt htH]

theorem exists_complete_common_regular_height (q : ℕ) [NeZero q] {y r : ℝ}
    (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧
      (∀ chi : Character q, ∀ t : ℝ, y ≤ t → t ≤ H →
        CompleteExpansion.zeroValues chi t = CompleteExpansion.zeroValues chi y) ∧
      (∀ chi : Character q, ∀ rho : ℂ, 1 / 2 ≤ rho.re → rho.re < 1 →
        |rho.im| = H → chi.LFunction rho ≠ 0) := by
  obtain ⟨H, hyH, hHr, hvalues, hreg⟩ := exists_common_regular_height q hr
  refine ⟨H, hyH, hHr, ?_, ?_⟩
  · intro chi t hyt htH
    simpa only [half_values_eq_complete] using hvalues chi (1 / 2) t hyt htH
  · intro chi rho h0 h1 ht
    exact hreg chi rho (by linarith) h1 ht

end LiuWang.Proof.DirichletZeroCount.Applications
