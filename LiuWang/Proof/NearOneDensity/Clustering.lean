import LiuWang.Proof.NearOneDensity.Quadratic
import Mathlib.Data.Finset.Max

set_option autoImplicit false
noncomputable section

open Classical

namespace LiuWang.Proof.NearOneDensity

/-- Closed local windows of occupancy at most `m` yield a separated subfamily
of at least a `1/m` fraction. Labels separate different characters, not zeros. -/
theorem exists_separated_subfamily {ι κ : Type*} (s : Finset ι)
    (label : ι → κ) (height : ι → ℝ) {b : ℝ} (hb : 0 ≤ b) (m : ℕ)
    (hlocal : ∀ k t, (s.filter (fun i => label i = k ∧ |height i - t| ≤ b)).card ≤ m) :
    ∃ u ⊆ s, s.card ≤ m * u.card ∧
      ∀ i ∈ u, ∀ j ∈ u, i ≠ j → label i = label j → 2 * b < |height i - height j| := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hmin⟩ := s.exists_min_image height hs
      let c := s.filter (fun j => label j = label i ∧ |height j - (height i + b)| ≤ b)
      have hcs : c ⊆ s := Finset.filter_subset _ _
      have hic : i ∈ c := by
        exact Finset.mem_filter.mpr
          ⟨hi, rfl, by rw [abs_of_nonpos (by linarith)]; linarith⟩
      have hc : c.card ≤ m := hlocal (label i) (height i + b)
      obtain ⟨u, hu, hcard, hsep⟩ := ih (s \ c) (Finset.sdiff_ssubset hcs ⟨i, hic⟩)
        (fun k t => (Finset.card_le_card
          (show (s \ c).filter (fun j => label j = k ∧ |height j - t| ≤ b) ⊆
              s.filter (fun j => label j = k ∧ |height j - t| ≤ b) from
            fun j hj => by
              rcases Finset.mem_filter.mp hj with ⟨hj, hp⟩
              exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, hp⟩)).trans
          (hlocal k t))
      have hiu : i ∉ u := by
        intro h
        exact (Finset.mem_sdiff.mp (hu h)).2 hic
      have hfar : ∀ j ∈ u, label i = label j → 2 * b < |height i - height j| := by
        intro j hj hl
        have hjparts := Finset.mem_sdiff.mp (hu hj)
        have hge := hmin j hjparts.1
        have hnot : ¬ |height j - (height i + b)| ≤ b := by
          intro h
          exact hjparts.2 (Finset.mem_filter.mpr ⟨hjparts.1, hl.symm, h⟩)
        have hgt : height i + 2 * b < height j := by
          by_contra! h
          apply hnot
          rw [abs_le]
          constructor <;> linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
      refine ⟨insert i u, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hi (hu.trans Finset.sdiff_subset)
      · have hcadd : (s \ c).card + c.card = s.card := by
          simpa only [Finset.inter_eq_right.mpr hcs] using Finset.card_sdiff_add_card_inter s c
        rw [Finset.card_insert_of_notMem hiu]
        nlinarith
      · intro j hj k hk hjk hl
        by_cases hji : j = i
        · subst j
          exact hfar k (Finset.mem_insert.mp hk |>.resolve_left hjk.symm) hl
        have hj' : j ∈ u := (Finset.mem_insert.mp hj).resolve_left hji
        by_cases hki : k = i
        · subst k
          rw [abs_sub_comm]
          exact hfar j hj' hl.symm
        · exact hsep j hj' k ((Finset.mem_insert.mp hk).resolve_left hki) hjk hl
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
      · simp

end LiuWang.Proof.NearOneDensity
