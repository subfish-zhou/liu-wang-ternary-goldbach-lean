import LiuWang.Proof.Campaign20260915.ZetaWinding.CountingIntegral

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

def criticalBlockValues (a b : ℝ) : Finset ℂ :=
  (positiveValues b).filter (fun z => z.re = 1 / 2 ∧ a ≤ z.im ∧ z.im < b)

def criticalBlockCount (a b : ℝ) : ℕ :=
  ∑ z ∈ criticalBlockValues a b, analyticOrderNatAt riemannZeta z

theorem positive_order_one_le {b : ℝ} {z : ℂ} (hz : z ∈ positiveValues b) :
    1 ≤ analyticOrderNatAt riemannZeta z :=
  zeta_order_positive_of_mem (Finset.mem_filter.mp hz).1

theorem card_le_criticalBlockCount {a b : ℝ} (F : Finset ℂ)
    (hF : F ⊆ criticalBlockValues a b) : F.card ≤ criticalBlockCount a b := by
  calc
    F.card = ∑ _z ∈ F, (1 : ℕ) := by simp
    _ ≤ ∑ z ∈ F, analyticOrderNatAt riemannZeta z :=
      Finset.sum_le_sum (fun z hz => positive_order_one_le (Finset.mem_filter.mp (hF hz)).1)
    _ ≤ _ := Finset.sum_le_sum_of_subset hF

theorem finite_zero_count_increment {a b : ℝ} (hab : a < b) (F : Finset ℂ)
    (hF : F ⊆ positiveValues b)
    (hlo : ∀ z ∈ F, a < z.im) (hhi : ∀ z ∈ F, z.im < b) :
    positiveCount a + F.card ≤ positiveCountLeft b := by
  classical
  have hd : Disjoint (positiveValues a) F := by
    apply Finset.disjoint_left.mpr
    intro z hz hf
    exact (not_lt.mpr (mem_positiveValues.mp hz).2.2.2.2) (hlo z hf)
  have hsub : positiveValues a ∪ F ⊆ (positiveValues b).filter (fun z => z.im < b) := by
    intro z hz
    rcases Finset.mem_union.mp hz with ha | hf
    · obtain ⟨hz, h0, h1, hp, ht⟩ := mem_positiveValues.mp ha
      exact Finset.mem_filter.mpr
        ⟨mem_positiveValues.mpr ⟨hz, h0, h1, hp, ht.trans hab.le⟩, ht.trans_lt hab⟩
    · exact Finset.mem_filter.mpr ⟨hF hf, hhi z hf⟩
  have hw : F.card ≤ ∑ z ∈ F, analyticOrderNatAt riemannZeta z := by
    calc
      _ = ∑ _z ∈ F, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z hz => positive_order_one_le (hF hz))
  have hs := Finset.sum_le_sum_of_subset (f := analyticOrderNatAt riemannZeta) hsub
  rw [Finset.sum_union hd] at hs
  change positiveCount a + _ ≤ positiveCountLeft b at hs
  omega

theorem criticalBlockCount_add_le_strictCount {a b : ℝ} (hab : a < b)
    (ha : riemannZeta (criticalPoint a) ≠ 0) :
    positiveCount a + criticalBlockCount a b ≤ positiveCountLeft b := by
  classical
  have hlo (z : ℂ) (hz : z ∈ criticalBlockValues a b) : a < z.im := by
    obtain ⟨hm, hr, hl, _⟩ := Finset.mem_filter.mp hz
    apply lt_of_le_of_ne hl
    intro he
    have hz' : z = criticalPoint a := by
      apply Complex.ext
      · exact hr
      · exact he.symm
    exact ha (hz' ▸ (mem_positiveValues.mp hm).1)
  have hd : Disjoint (positiveValues a) (criticalBlockValues a b) := by
    apply Finset.disjoint_left.mpr
    intro z hz hf
    exact (not_lt.mpr (mem_positiveValues.mp hz).2.2.2.2) (hlo z hf)
  have hsub : positiveValues a ∪ criticalBlockValues a b ⊆
      (positiveValues b).filter (fun z => z.im < b) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨hz, h0, h1, hp, ht⟩ := mem_positiveValues.mp hz
      exact Finset.mem_filter.mpr
        ⟨mem_positiveValues.mpr ⟨hz, h0, h1, hp, ht.trans hab.le⟩, ht.trans_lt hab⟩
    · obtain ⟨hm, _, _, ht⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hm, ht⟩
  have hs := Finset.sum_le_sum_of_subset (f := analyticOrderNatAt riemannZeta) hsub
  rw [Finset.sum_union hd] at hs
  exact hs

theorem baseline_zero_area {a b : ℝ} :
    (∑ z ∈ positiveValues a, (analyticOrderNatAt riemannZeta z : ℝ) *
      (b - max a z.im)) = (positiveCount a : ℝ) * (b - a) := by
  have he : ∀ z ∈ positiveValues a, max a z.im = a :=
    fun z hz => max_eq_left (mem_positiveValues.mp hz).2.2.2.2
  simp_rw [positiveCount, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun z hz => by rw [he z hz])

theorem finite_zero_left_area {a b : ℝ} (hab : a ≤ b) (F : Finset ℂ)
    (hF : F ⊆ positiveValues b) (hlo : ∀ z ∈ F, a < z.im) :
    (positiveCount a : ℝ) * (b - a) +
      (∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (b - z.im)) ≤
        ∫ t in a..b, (positiveCount t : ℝ) := by
  classical
  have hd : Disjoint (positiveValues a) F := by
    apply Finset.disjoint_left.mpr
    intro z hz hf
    exact (not_lt.mpr (mem_positiveValues.mp hz).2.2.2.2) (hlo z hf)
  have hsub : positiveValues a ∪ F ⊆ positiveValues b := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨hz, h0, h1, hp, ht⟩ := mem_positiveValues.mp hz
      exact mem_positiveValues.mpr ⟨hz, h0, h1, hp, ht.trans hab⟩
    · exact hF hz
  have hs := zero_area_lower_bound hab (positiveValues a ∪ F) hsub
  rw [Finset.sum_union hd, baseline_zero_area] at hs
  have hf : (∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (b - max a z.im)) =
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (b - z.im) :=
    Finset.sum_congr rfl (fun z hz => by rw [max_eq_right (hlo z hz).le])
  rw [hf, integral_turingS_eq_zero_areas hab] at hs
  rw [integral_positiveCount_eq_zero_areas hab]
  linarith

theorem integral_strictCount_deficit {a b : ℝ} (hab : a ≤ b) :
    (positiveCountLeft b : ℝ) * (b - a) - (∫ t in a..b, (positiveCount t : ℝ)) =
      ∑ z ∈ (positiveValues b).filter (fun z => z.im < b),
        (analyticOrderNatAt riemannZeta z : ℝ) * (max a z.im - a) := by
  classical
  have hi : (∫ t in a..b, (positiveCount t : ℝ)) =
      ∑ z ∈ (positiveValues b).filter (fun z => z.im < b),
        (analyticOrderNatAt riemannZeta z : ℝ) * (b - max a z.im) := by
    rw [integral_positiveCount_eq_zero_areas hab, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs with h
    · rfl
    · have he : z.im = b :=
        le_antisymm (mem_positiveValues.mp hz).2.2.2.2 (not_lt.mp h)
      simp [he, max_eq_right hab]
  rw [hi, positiveCountLeft, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem finite_zero_right_area {a b : ℝ} (hab : a ≤ b) (F : Finset ℂ)
    (hF : F ⊆ positiveValues b) (hlo : ∀ z ∈ F, a ≤ z.im)
    (hhi : ∀ z ∈ F, z.im < b) :
    (∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (z.im - a)) ≤
      (positiveCountLeft b : ℝ) * (b - a) -
        (∫ t in a..b, (positiveCount t : ℝ)) := by
  classical
  rw [integral_strictCount_deficit hab]
  have hsub : F ⊆ (positiveValues b).filter (fun z => z.im < b) :=
    fun z hz => Finset.mem_filter.mpr ⟨hF hz, hhi z hz⟩
  calc
    _ = ∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (max a z.im - a) :=
      Finset.sum_congr rfl (fun z hz => by rw [max_eq_right (hlo z hz)])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z _ _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (le_max_left _ _)))

#print axioms criticalBlockCount_add_le_strictCount
#print axioms finite_zero_count_increment
#print axioms finite_zero_left_area
#print axioms integral_strictCount_deficit
#print axioms finite_zero_right_area

end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
