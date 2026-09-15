import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceFreeConsumers

/-! The actual closed short-window source, kept distinct from the frozen strict PaperSource. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.LowSum

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

def ClosedPaperSource (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : Prop :=
  (d.modulus : ℝ) ≤ sourceP N ∧ datumL d e = 0 ∧ e.im = 0 ∧ e.re < 1 ∧ paperCap N ≤ e.re

theorem paperSource_closed {N : ℕ} {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) : ClosedPaperSource N d e :=
  ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.le⟩

theorem closed_source_strict_or_boundary {N : ℕ} {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : ClosedPaperSource N d e) : PaperSource N d e ∨ e.re = paperCap N := by
  rcases lt_or_eq_of_le hd.2.2.2.2 with hh | hh
  · exact Or.inl ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hh⟩
  · exact Or.inr hh.symm

theorem closed_source_of_short_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (ht : |rho.im| ≤ sourceP N / q) (hb : paperCap N ≤ rho.re) :
    ∃ d : PrimitiveQuadraticDatum, ClosedPaperSource N d rho ∧
      d.modulus = chi.conductor ∧ d.modulus ∣ q ∧ inducedAt d q = chi := by
  obtain ⟨hc, h2, hi, _⟩ := original_short_classification_closed hN hq hr ht hb
  have hm := CompleteExpansion.mem_zeroValues.mp hr
  refine ⟨primitiveSource chi hc h2, ?_, rfl, chi.conductor_dvd_level,
    inducedAt_primitiveSource chi hc h2⟩
  refine ⟨?_, primitiveSource_zero chi hc h2 hm.2.1 hm.1, hi, hm.2.2.1, hb⟩
  exact (show (chi.conductor : ℝ) ≤ q by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq

theorem closed_source_unique {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d f : PrimitiveQuadraticDatum} {e z : ℂ}
    (hd : ClosedPaperSource N d e) (hf : ClosedPaperSource N f z) : d = f ∧ e = z := by
  have hx := sourceP_original_scale hN
  have he : (e.re : ℂ) = e := by apply Complex.ext <;> simp [hd.2.2.1]
  have hz : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hf.2.2.1]
  have hdf := SourceRoute.Exception.Restart.real_sources_unique_original d f
    (by linarith : 10 ≤ sourceP N) hd.1 hf.1 hd.2.2.2.2 hf.2.2.2.2
    (by simpa only [he] using hd.2.1) (by simpa only [hz] using hf.2.1)
  subst f
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have ht : 0 ≤ sourceP N / d.modulus := by
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hzero := source_free_original_zeros_equal_closed hx hd.1 d.character d.character
    hd.2.2.2.2 hd.2.2.2.1 hf.2.2.2.2 hf.2.2.2.1
    (by simpa only [hd.2.2.1, abs_zero] using ht)
    (by simpa only [hf.2.2.1, abs_zero] using ht) hd.2.1 hf.2.1
  exact ⟨rfl, hzero.2⟩

theorem closed_induced_mem {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    e ∈ CompleteExpansion.zeroValues (inducedAt d q) (omegaCutoff N q) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hz : (inducedAt d q).LFunction e = 0 := by
    rw [inducedAt, dif_pos hdiv,
      DirichletCharacter.LFunction_changeLevel hdiv d.character (Or.inl d.ne_one)]
    change datumL d e * _ = 0
    rw [hd.2.1, zero_mul]
  have hh := SourceRoute.Exception.Restart.original_re_half
    (by linarith [sourceP_original_scale hN] : 10 ≤ sourceP N) hd.2.2.2.2
  exact CompleteExpansion.mem_zeroValues.mpr ⟨hz, by linarith, hd.2.2.2.1,
    by rw [hd.2.2.1, abs_zero]; linarith [omegaCutoff_ge (NeZero.pos q) hq], hh.le⟩

theorem closed_short_zero_iff {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e)
    (chi : Character q) (rho : ℂ) :
    (rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) ∧
      |rho.im| ≤ sourceP N / q ∧ paperCap N ≤ rho.re) ↔
        d.modulus ∣ q ∧ chi = inducedAt d q ∧ rho = e := by
  constructor
  · rintro ⟨hr, ht, hb⟩
    obtain ⟨f, hf, _, hdiv, hchi⟩ := closed_source_of_short_zero hN hq hr ht hb
    obtain ⟨rfl, rfl⟩ := closed_source_unique hN hd hf
    exact ⟨hdiv, hchi.symm, rfl⟩
  · rintro ⟨hdiv, rfl, rfl⟩
    exact ⟨closed_induced_mem hN hq hd hdiv,
      by rw [hd.2.2.1, abs_zero]
         exact div_nonneg (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le (Nat.cast_nonneg q),
      hd.2.2.2.2⟩

theorem closed_source_short_absence_iff {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e) :
    (∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N) ↔ ¬d.modulus ∣ q := by
  constructor
  · intro hh hdiv
    have hz := (closed_short_zero_iff hN hq hd (inducedAt d q) e).mpr ⟨hdiv, rfl, rfl⟩
    exact (not_lt_of_ge hz.2.2) (hh _ _ hz.1 hz.2.1)
  · intro hdiv chi rho hr ht
    exact lt_of_not_ge (fun hb => hdiv ((closed_short_zero_iff hN hq hd chi rho).mp
      ⟨hr, ht, hb⟩).1)

theorem closed_source_multiplicity {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e)
    (hdiv : d.modulus ∣ q) : zeroMultiplicity (inducedAt d q) e = 1 := by
  have hz := (closed_short_zero_iff hN hq hd (inducedAt d q) e).mpr ⟨hdiv, rfl, rfl⟩
  exact (original_short_classification_closed hN hq hz.1 hz.2.1 hz.2.2).2.2.2

theorem closed_short_filter_eq {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e)
    (chi : Character q) :
    (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
      (fun rho => |rho.im| ≤ sourceP N / q ∧ paperCap N ≤ rho.re) =
        if d.modulus ∣ q ∧ chi = inducedAt d q then {e} else ∅ := by
  ext rho
  simp only [Finset.mem_filter]
  rw [closed_short_zero_iff hN hq hd chi]
  by_cases hc : d.modulus ∣ q ∧ chi = inducedAt d q
  · simp only [if_pos hc, Finset.mem_singleton]
    exact ⟨fun h => h.2.2, fun h => ⟨hc.1, hc.2, h⟩⟩
  · simp only [if_neg hc, Finset.notMem_empty, iff_false]
    exact fun h => hc ⟨h.1, h.2.1⟩

theorem closed_short_multiplicity_sum {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e)
    (chi : Character q) :
    (∑ rho ∈ (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
      (fun rho => |rho.im| ≤ sourceP N / q ∧ paperCap N ≤ rho.re),
        zeroMultiplicity chi rho) =
      if d.modulus ∣ q ∧ chi = inducedAt d q then 1 else 0 := by
  rw [closed_short_filter_eq hN hq hd chi]
  by_cases hc : d.modulus ∣ q ∧ chi = inducedAt d q
  · simp only [if_pos hc, Finset.sum_singleton]
    rw [hc.2]
    exact closed_source_multiplicity hN hq hd hc.1
  · simp only [if_neg hc, Finset.sum_empty]

theorem no_closed_source_short_absence {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ d e, ClosedPaperSource N d e) :
    ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N := by
  intro chi rho hr ht
  apply lt_of_not_ge
  intro hb
  obtain ⟨d, hd, _⟩ := closed_source_of_short_zero hN hq hr ht hb
  exact hnone ⟨d, rho, hd⟩

theorem boundary_source_no_strict {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e)
    (he : e.re = paperCap N) : ¬ ∃ f z, PaperSource N f z := by
  rintro ⟨f, z, hf⟩
  have hz := (closed_source_unique hN hd (paperSource_closed hf)).2
  have hb := hf.2.2.2.2
  change paperCap N < z.re at hb
  rw [← hz, he] at hb
  exact lt_irrefl _ hb

theorem no_closed_source_iff_all_short_absence {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (¬ ∃ d e, ClosedPaperSource N d e) ↔
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
        ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
          |rho.im| ≤ sourceP N / q → rho.re < paperCap N := by
  constructor
  · exact fun hn q _ hq => no_closed_source_short_absence (q := q) hN hq hn
  · intro hh
    rintro ⟨d, e, hd⟩
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    exact ((closed_source_short_absence_iff hN hd.1 hd).mp
      (hh d.modulus hd.1)) (dvd_refl d.modulus)

theorem no_strict_source_closed_dichotomy {N : ℕ}
    (hnone : ¬ ∃ d e, PaperSource N d e) :
    (¬ ∃ d e, ClosedPaperSource N d e) ∨
      ∃ d e, ClosedPaperSource N d e ∧ e.re = paperCap N := by
  by_cases hex : ∃ d e, ClosedPaperSource N d e
  · obtain ⟨d, e, hd⟩ := hex
    rcases closed_source_strict_or_boundary hd with hs | he
    · exact False.elim (hnone ⟨d, e, hs⟩)
    · exact Or.inr ⟨d, e, hd, he⟩
  · exact Or.inl hex

end LiuWang.Proof.Campaign20260915.OriginalRegion
