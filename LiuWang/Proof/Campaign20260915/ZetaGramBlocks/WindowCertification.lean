import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.SignAreas

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

def openWindowValues (a b : ℝ) : Finset ℂ :=
  (positiveValues b).filter (fun z => a < z.im ∧ z.im < b)

theorem openWindow_count_identity {a b : ℝ} (hab : a < b) :
    positiveCount a + (∑ z ∈ openWindowValues a b, analyticOrderNatAt riemannZeta z) =
      positiveCountLeft b := by
  classical
  have hd : Disjoint (positiveValues a) (openWindowValues a b) := by
    apply Finset.disjoint_left.mpr
    intro z ha hb
    exact (not_lt.mpr (mem_positiveValues.mp ha).2.2.2.2) (Finset.mem_filter.mp hb).2.1
  have he : positiveValues a ∪ openWindowValues a b =
      (positiveValues b).filter (fun z => z.im < b) := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨hz, h0, h1, hp, ht⟩ := mem_positiveValues.mp hz
        exact Finset.mem_filter.mpr
          ⟨mem_positiveValues.mpr ⟨hz, h0, h1, hp, ht.trans hab.le⟩, ht.trans_lt hab⟩
      · exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.2⟩
    · intro hz
      obtain ⟨hm, hlt⟩ := Finset.mem_filter.mp hz
      by_cases ha : z.im ≤ a
      · apply Finset.mem_union_left
        obtain ⟨hz, h0, h1, hp, _⟩ := mem_positiveValues.mp hm
        exact mem_positiveValues.mpr ⟨hz, h0, h1, hp, ha⟩
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, not_le.mp ha, hlt⟩)
  have hs := congrArg (fun F : Finset ℂ => ∑ z ∈ F, analyticOrderNatAt riemannZeta z) he
  rw [Finset.sum_union hd] at hs
  exact hs

theorem openWindow_exhaustion {a b : ℝ} (hab : a < b) (F : Finset ℂ)
    (hF : F ⊆ openWindowValues a b)
    (hupper : positiveCountLeft b ≤ positiveCount a + F.card) :
    openWindowValues a b = F ∧
      ∀ z ∈ openWindowValues a b, analyticOrderNatAt riemannZeta z = 1 := by
  classical
  have hc := openWindow_count_identity hab
  have hsum : (∑ z ∈ openWindowValues a b, analyticOrderNatAt riemannZeta z) ≤ F.card := by
    omega
  have hcard : (openWindowValues a b).card ≤
      ∑ z ∈ openWindowValues a b, analyticOrderNatAt riemannZeta z := by
    calc
      _ = ∑ _z ∈ openWindowValues a b, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z hz => positive_order_one_le (Finset.mem_filter.mp hz).1)
  have he : openWindowValues a b = F :=
    (Finset.eq_of_subset_of_card_le hF (hcard.trans hsum)).symm
  refine ⟨he, ?_⟩
  intro z hz
  have hp := positive_order_one_le (Finset.mem_filter.mp hz).1
  by_contra hn
  have hgt : 1 < analyticOrderNatAt riemannZeta z := by omega
  have hh : (∑ _w ∈ openWindowValues a b, (1 : ℕ)) <
      ∑ w ∈ openWindowValues a b, analyticOrderNatAt riemannZeta w :=
    Finset.sum_lt_sum (fun w hw => positive_order_one_le (Finset.mem_filter.mp hw).1)
      ⟨z, hz, hgt⟩
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hh
  rw [he] at hh hsum
  omega

theorem signed_window_complete_of_count_upper {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {m : ℕ} (l r : Fin m → ℝ) (hlo : ∀ i, a ≤ l i) (hhi : ∀ i, r i ≤ b)
    (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0)
    (hupper : positiveCountLeft b ≤ positiveCount a + m) :
    positiveCountLeft b = positiveCount a + m ∧
      ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
        a < z.im → z.im < b → z.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta z = 1 := by
  obtain ⟨F, hcard, hf, hl, hh, hr, _, _⟩ :=
    sign_window_evidence ha l r hlo hhi hwidth hsep hsign
  have hsub : F ⊆ openWindowValues a b :=
    fun z hz => Finset.mem_filter.mpr ⟨hf hz, hl z hz, hh z hz⟩
  have hex := openWindow_exhaustion hab F hsub (by rwa [hcard])
  have hlow := finite_zero_count_increment hab F hf hl hh
  rw [hcard] at hlow
  refine ⟨le_antisymm hupper hlow, ?_⟩
  intro z hz h0 h1 hza hzb
  have hm : z ∈ openWindowValues a b := Finset.mem_filter.mpr
    ⟨mem_positiveValues.mpr ⟨hz, h0, h1, ha.trans_lt hza, hzb.le⟩, hza, hzb⟩
  exact ⟨hr z (hex.1 ▸ hm), hex.2 z hm⟩

theorem strict_closed_count_eq_iff (T : ℝ) :
    positiveCountLeft T = positiveCount T ↔ boundaryMultiplicity T = 0 := by
  have h := positiveCount_jump T
  omega

#print axioms openWindow_count_identity
#print axioms openWindow_exhaustion
#print axioms signed_window_complete_of_count_upper
#print axioms strict_closed_count_eq_iff

end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
