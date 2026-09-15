import LiuWang.Proof.SourceRoute.Density.Restart.FamilyMaximum

/-! Open or closed common-height windows have the same supremum for this continuous family. -/

set_option autoImplicit false

noncomputable section

open Complex Set

namespace LiuWang.Proof.SourceRoute.Density.Restart

theorem continuous_sup_closed_open {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    sSup (f '' Icc a b) = sSup (f '' Ioo a b) := by
  have hbc : BddAbove (f '' Icc a b) := isCompact_Icc.bddAbove_image hf.continuousOn
  have hbo : BddAbove (f '' Ioo a b) := hbc.mono (image_mono Ioo_subset_Icc_self)
  have hno : (f '' Ioo a b).Nonempty := (nonempty_Ioo.mpr hab).image f
  have hnc : (f '' Icc a b).Nonempty := (nonempty_Icc.mpr hab.le).image f
  apply le_antisymm
  · apply csSup_le hnc
    rintro _ ⟨t, ht, rfl⟩
    have hle : ∀ t ∈ Ioo a b, f t ≤ sSup (f '' Ioo a b) :=
      fun t ht => le_csSup hbo (mem_image_of_mem f ht)
    have hc := le_on_closure hle hf.continuousOn continuousOn_const
    rw [closure_Ioo hab.ne] at hc
    exact hc ht
  · exact csSup_le_csSup hbc hno (image_mono Ioo_subset_Icc_self)

theorem familyWindow_eq_open (q : ℕ) [NeZero q] (X sigma T : ℝ) :
    familyWindow q X sigma T =
      sSup ((fun t : ℝ => familySquare q X ((sigma : ℂ) + t * I)) ''
        Ioo (T - 3 / 2) (T + 3 / 2)) :=
  continuous_sup_closed_open ((familySquare_continuous q X).comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))) (by linarith)

theorem familyWindow_le_iff (q : ℕ) [NeZero q] (X sigma T C : ℝ) :
    familyWindow q X sigma T ≤ C ↔
      ∀ t, |t - T| < 3 / 2 → familySquare q X ((sigma : ℂ) + t * I) ≤ C := by
  constructor
  · intro h t ht
    exact (familySquare_le_window q X sigma T ht.le).trans h
  · intro h
    rw [familyWindow_eq_open]
    apply csSup_le ((nonempty_Ioo.mpr (by linarith : T - 3 / 2 < T + 3 / 2)).image _)
    rintro _ ⟨t, ht, rfl⟩
    exact h t (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

end LiuWang.Proof.SourceRoute.Density.Restart
