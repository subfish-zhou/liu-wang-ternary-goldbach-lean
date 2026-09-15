import LiuWang.Proof.Campaign20260915.ZetaWinding.CountEnclosure

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem witnesses_above_sixteen {H : ℝ} (hH : 16 ≤ H) {m : ℕ}
    (l r : Fin m → ℝ) (hlo : ∀ i, 16 ≤ l i) (hhi : ∀ i, r i ≤ H)
    (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0) :
    ∃ w : Finset ℂ, w.card = 2 + 2 * m ∧
      ∀ s ∈ w, riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ |s.im| ≤ H := by
  classical
  obtain ⟨z, hinj, hz⟩ := exists_injective_critical_zeros l r hwidth hsep hsign
  have hzlo (i : Fin m) : 16 < (z i).im := (hlo i).trans_lt (hz i).2.2.1
  have hzhi (i : Fin m) : (z i).im < H := (hz i).2.2.2.trans_le (hhi i)
  let p : Finset ℂ := Finset.univ.image z
  let q : Finset ℂ := p.image conj
  have hp (s : ℂ) (hs : s ∈ p) :
      riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ 16 < s.im ∧ s.im < H := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hz i).1, (hz i).2.1, hzlo i, hzhi i⟩
  have hq (s : ℂ) (hs : s ∈ q) :
      riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ s.im < -16 ∧ -s.im < H := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    have hh := hp v hv
    refine ⟨by rw [riemannZeta_conj, hh.1, map_zero], by simpa using hh.2.1, ?_, ?_⟩
    · simp only [conj_im]; linarith [hh.2.2.1]
    · simpa only [conj_im, neg_neg] using hh.2.2.2
  have hpc : p.card = m := by
    simp only [p, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hqc : q.card = m := by
    change (p.image conj).card = m
    rw [Finset.card_image_of_injective _ (starRingEnd ℂ).injective, hpc]
  have hpq : Disjoint p q := by
    apply Finset.disjoint_left.mpr
    intro s hsp hsq
    linarith [(hp s hsp).2.2.1, (hq s hsq).2.2.1]
  have hb : (zetaClosedValues 16).card = 2 := by
    obtain ⟨t, ht, he⟩ := zetaClosedValues_sixteen_pair
    have hn : criticalPoint t ≠ conj (criticalPoint t) := by
      intro hh
      have hi := congrArg Complex.im hh
      simp only [criticalPoint, conj_im] at hi
      linarith [ht.1]
    rw [he, Finset.card_pair hn]
  have hdis : Disjoint (zetaClosedValues 16) (p ∪ q) := by
    apply Finset.disjoint_left.mpr
    intro s hsb hsn
    have hbnd := (abs_le.mp (mem_zetaClosedValues.mp hsb).2.2.2)
    rcases Finset.mem_union.mp hsn with hsp | hsq
    · linarith [(hp s hsp).2.2.1]
    · linarith [(hq s hsq).2.2.1]
  refine ⟨zetaClosedValues 16 ∪ (p ∪ q), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hpq,
      hb, hpc, hqc]
    omega
  · intro s hs
    rcases Finset.mem_union.mp hs with hsb | hsn
    · have hh := mem_zetaClosedValues.mp hsb
      exact ⟨hh.1, (zeta_sixteen_all_simple_on_line hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).1,
        hh.2.2.2.trans hH⟩
    · rcases Finset.mem_union.mp hsn with hsp | hsq
      · have hh := hp s hsp
        exact ⟨hh.1, hh.2.1, by rw [abs_of_pos (by linarith [hh.2.2.1])]; exact hh.2.2.2.le⟩
      · have hh := hq s hsq
        exact ⟨hh.1, hh.2.1, by rw [abs_of_neg (by linarith [hh.2.2.1])]; exact hh.2.2.2.le⟩

theorem zeta_all_simple_of_segments_and_signs {H : ℝ} (hH : 16 ≤ H)
    (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
    (hs : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)), 1 / 2 ≤ t)
    (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
      0 < (c j * riemannZeta (horizontalAt H t)).re)
    {m : ℕ} (l r : Fin m → ℝ) (hlo : ∀ i, 16 ≤ l i) (hhi : ∀ i, r i ≤ H)
    (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0)
    (hu : 2 * (xiCountingPrimitive (horizontalAt H 2) -
        xiCountingPrimitive 2 - horizontalPrimitiveSum H x c n).im <
          (3 + 2 * (m : ℝ)) * Real.pi) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → |s.im| ≤ H →
      s.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta s = 1 := by
  obtain ⟨w, hwcard, hw⟩ := witnesses_above_sixteen hH l r hlo hhi hwidth hsep hsign
  apply zeta_all_simple_of_segment_upper_and_witnesses (by linarith) x c n hx0 hxn hs hr w hw
  rw [hwcard]
  convert hu using 1
  push_cast
  ring

#print axioms witnesses_above_sixteen
#print axioms zeta_all_simple_of_segments_and_signs

end LiuWang.Proof.Campaign20260915.ZetaWinding
