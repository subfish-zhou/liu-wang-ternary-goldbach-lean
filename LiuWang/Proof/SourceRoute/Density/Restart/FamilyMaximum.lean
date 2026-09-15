import LiuWang.Proof.SourceRoute.Density.Restart.FamilyProduct

/-! Sum over all characters first, then maximize at a common height and real part. -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric

namespace LiuWang.Proof.SourceRoute.Density.Restart

def familyWindow (q : ℕ) [NeZero q] (X sigma T : ℝ) : ℝ :=
  sSup ((fun t : ℝ => familySquare q X ((sigma : ℂ) + t * I)) '' Icc (T - 3 / 2) (T + 3 / 2))

def familyMaximum (q : ℕ) [NeZero q] (X T a b : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => familySquare q X ((p.1 : ℂ) + p.2 * I)) ''
    (Icc a b ×ˢ Icc (T - 3 / 2) (T + 3 / 2)))

theorem familyWindow_bddAbove (q : ℕ) [NeZero q] (X sigma T : ℝ) :
    BddAbove ((fun t : ℝ => familySquare q X ((sigma : ℂ) + t * I)) ''
      Icc (T - 3 / 2) (T + 3 / 2)) :=
  isCompact_Icc.bddAbove_image
    ((familySquare_continuous q X).comp (continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const))).continuousOn

theorem familyMaximum_bddAbove (q : ℕ) [NeZero q] (X T a b : ℝ) :
    BddAbove ((fun p : ℝ × ℝ => familySquare q X ((p.1 : ℂ) + p.2 * I)) ''
      (Icc a b ×ˢ Icc (T - 3 / 2) (T + 3 / 2))) :=
  (isCompact_Icc.prod isCompact_Icc).bddAbove_image ((familySquare_continuous q X).comp
    ((Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))).continuousOn

theorem familySquare_le_window (q : ℕ) [NeZero q] (X sigma T : ℝ) {t : ℝ}
    (ht : |t - T| ≤ 3 / 2) : familySquare q X ((sigma : ℂ) + t * I) ≤ familyWindow q X sigma T :=
  le_csSup (familyWindow_bddAbove q X sigma T)
    (mem_image_of_mem _ ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩)

theorem familySquare_le_maximum (q : ℕ) [NeZero q] (X T : ℝ) {a b sigma t : ℝ}
    (hs : sigma ∈ Icc a b) (ht : |t - T| ≤ 3 / 2) :
    familySquare q X ((sigma : ℂ) + t * I) ≤ familyMaximum q X T a b :=
  le_csSup (familyMaximum_bddAbove q X T a b)
    ⟨(sigma, t), ⟨hs, ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩⟩, rfl⟩

theorem familyWindow_le_maximum (q : ℕ) [NeZero q] (X T : ℝ) {a b sigma : ℝ}
    (hs : sigma ∈ Icc a b) : familyWindow q X sigma T ≤ familyMaximum q X T a b := by
  apply csSup_le
  · exact ⟨_, ⟨T, ⟨by linarith, by linarith⟩, rfl⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact familySquare_le_maximum q X T hs (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

theorem familyMaximum_eq_nested (q : ℕ) [NeZero q] (X T : ℝ) {a b : ℝ} (hab : a ≤ b) :
    familyMaximum q X T a b = sSup ((fun sigma => familyWindow q X sigma T) '' Icc a b) := by
  have hB : BddAbove ((fun sigma => familyWindow q X sigma T) '' Icc a b) :=
    ⟨familyMaximum q X T a b, by rintro _ ⟨sigma, hs, rfl⟩; exact familyWindow_le_maximum q X T hs⟩
  have hn : ((fun p : ℝ × ℝ => familySquare q X ((p.1 : ℂ) + p.2 * I)) ''
      (Icc a b ×ˢ Icc (T - 3 / 2) (T + 3 / 2))).Nonempty :=
    ⟨_, ⟨(a, T), ⟨⟨le_rfl, hab⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩⟩
  have hn' : ((fun sigma => familyWindow q X sigma T) '' Icc a b).Nonempty :=
    ⟨familyWindow q X a T, a, ⟨le_rfl, hab⟩, rfl⟩
  apply le_antisymm
  · apply csSup_le hn
    rintro _ ⟨p, hp, rfl⟩
    exact (familySquare_le_window q X p.1 T
      (abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩)).trans
      (le_csSup hB (mem_image_of_mem _ hp.1))
  · apply csSup_le hn'
    rintro _ ⟨sigma, hs, rfl⟩
    exact familyWindow_le_maximum q X T hs

theorem familyMaximum_attained (q : ℕ) [NeZero q] (X T : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ sigma ∈ Icc a b, ∃ t, |t - T| ≤ 3 / 2 ∧
      familyMaximum q X T a b = familySquare q X ((sigma : ℂ) + t * I) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => familySquare q X ((p.1 : ℂ) + p.2 * I))
      (Icc a b ×ˢ Icc (T - 3 / 2) (T + 3 / 2)) := ((familySquare_continuous q X).comp
    ((Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))).continuousOn
  have hn : (Icc a b ×ˢ Icc (T - 3 / 2) (T + 3 / 2)).Nonempty :=
    ⟨(a, T), ⟨⟨le_rfl, hab⟩, ⟨by linarith, by linarith⟩⟩⟩
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn hn hc
  have ht : |p.2 - T| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  refine ⟨p.1, hp.1, p.2, ht, le_antisymm ?_ (familySquare_le_maximum q X T hp.1 ht)⟩
  apply csSup_le (hn.image _)
  rintro _ ⟨v, hv, rfl⟩
  exact hmax hv

theorem familyMaximum_nonneg (q : ℕ) [NeZero q] (X T : ℝ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ familyMaximum q X T a b :=
  (familySquare_nonneg q X _).trans
    (familySquare_le_maximum q X T ⟨le_rfl, hab⟩ (t := T) (by norm_num))

theorem shifted_familySquare_le_maximum (q : ℕ) [NeZero q] (X : ℝ) {T U R : ℝ}
    (hwin : |U - T| + R ≤ 3 / 2) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) R) :
    familySquare q X (s + U * I) ≤ familyMaximum q X T (2 - R) (2 + R) := by
  have hr : |s.re - 2| ≤ R := by
    simpa only [sub_re, show (2 : ℂ).re = 2 from rfl] using
      (Complex.abs_re_le_norm (s - 2)).trans (mem_closedBall_iff_norm.mp hs)
  have hi : |s.im| ≤ R := by
    simpa only [sub_im, show (2 : ℂ).im = 0 from rfl, sub_zero] using
      (Complex.abs_im_le_norm (s - 2)).trans (mem_closedBall_iff_norm.mp hs)
  have ht : |(s.im + U) - T| ≤ 3 / 2 := by
    calc
      _ = |s.im + (U - T)| := by congr 1; ring
      _ ≤ |s.im| + |U - T| := abs_add_le _ _
      _ ≤ 3 / 2 := by linarith only [hi, hwin]
  have hz : s + U * I = (s.re : ℂ) + ((s.im + U : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz]
  exact familySquare_le_maximum q X T (a := 2 - R) (b := 2 + R)
    (sigma := s.re) (t := s.im + U)
    ⟨by linarith only [(abs_le.mp hr).1], by linarith only [(abs_le.mp hr).2]⟩ ht

end LiuWang.Proof.SourceRoute.Density.Restart
