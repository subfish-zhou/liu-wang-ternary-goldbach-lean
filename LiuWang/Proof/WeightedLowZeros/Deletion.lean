import LiuWang.Proof.WeightedLowZeros.Exceptional

/-! # The single-source deleted term, with exact ordinary multiplicity -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros

theorem source_mem_iff {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e)
    (chi : Character q) :
    e ∈ CompleteExpansion.zeroValues chi (x / q) ↔
      d.modulus ∣ q ∧ chi = inducedAt d q := by
  have hheight : |e.im| ≤ x / q := by rw [hd.2.2.1, abs_zero]; positivity
  have hr : RealClosure.region x q e := ⟨hd.2.2.2.2, hheight⟩
  constructor
  · intro he
    have hm := CompleteExpansion.mem_zeroValues.mp he
    have hp : chi ≠ 1 ∨ e ≠ 1 := Or.inr (fun heq => by simp [heq] at hm)
    have hc := source_controls hx hd q hq chi e hr hp hm.1
    exact ⟨hc.2.2.1, hc.2.2.2.1.symm⟩
  · rintro ⟨hdq, rfl⟩
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    have hz : (inducedAt d q).LFunction e = 0 := by
      rw [inducedAt, dif_pos hdq,
        DirichletCharacter.LFunction_changeLevel hdq d.character (Or.inl d.ne_one)]
      change datumL d e * _ = 0
      rw [hd.2.1, zero_mul]
    exact CompleteExpansion.mem_zeroValues.mpr
      ⟨hz, (regionCap_pos hx).trans hd.2.2.2.2, hd.2.2.2.1, hheight,
        (RealClosure.region_re_half hx hr).le⟩

theorem source_multiplicity {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e) (hdq : d.modulus ∣ q) :
    zeroMultiplicity (inducedAt d q) e = 1 := by
  have he := (source_mem_iff hx hq hd (inducedAt d q)).mpr ⟨hdq, rfl⟩
  have hm := CompleteExpansion.mem_zeroValues.mp he
  have hp : inducedAt d q ≠ 1 ∨ e ≠ 1 := Or.inr (fun heq => by simp [heq] at hm)
  exact (source_controls hx hd q hq _ e ⟨hd.2.2.2.2, hm.2.2.2.1⟩ hp hm.1).2.2.2.2

theorem sum_split_retained {A : Type*} [AddCommMonoid A] {q : ℕ} [NeZero q]
    (y : ℝ) (d : PrimitiveQuadraticDatum) (e : ℂ) (f : Character q → ℂ → A) :
    (∑ chi : Character q, ∑ rho ∈ CompleteExpansion.zeroValues chi y, f chi rho) =
      (∑ chi : Character q, ∑ rho ∈ retainedValues chi y d e, f chi rho) +
        if e ∈ CompleteExpansion.zeroValues (inducedAt d q) y then f (inducedAt d q) e else 0 := by
  have hchi (chi : Character q) :
      (∑ rho ∈ CompleteExpansion.zeroValues chi y, f chi rho) =
        (∑ rho ∈ retainedValues chi y d e, f chi rho) +
          if chi = inducedAt d q then
            (if e ∈ CompleteExpansion.zeroValues chi y then f chi e else 0) else 0 := by
    by_cases hc : chi = inducedAt d q
    · subst chi
      have hset : retainedValues (inducedAt d q) y d e =
          (CompleteExpansion.zeroValues (inducedAt d q) y).erase e := by
        ext rho
        simp [retainedValues, Finset.mem_erase, and_comm, ne_comm]
      rw [hset, if_pos rfl]
      by_cases he : e ∈ CompleteExpansion.zeroValues (inducedAt d q) y
      · rw [if_pos he, Finset.sum_erase_add _ _ he]
      · rw [if_neg he, Finset.erase_eq_of_notMem he, add_zero]
    · simp [retainedValues, hc]
  simp_rw [hchi]
  rw [Finset.sum_add_distrib]
  simp

theorem weightedSum_split_source {N q : ℕ} [NeZero q] {x : ℝ}
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e) :
    (∑ chi : Character q, weightedSum N chi (x / q)) =
      retainedSum N q (x / q) d e + if d.modulus ∣ q then weight N e.re else 0 := by
  have h := sum_split_retained (q := q) (x / q) d e
    (fun chi rho => (zeroMultiplicity chi rho : ℝ) * weight N rho.re)
  simp only [source_mem_iff hx hq hd, and_true] at h
  by_cases hdq : d.modulus ∣ q
  · simpa only [weightedSum, retainedSum, if_pos hdq, source_multiplicity hx hq hd hdq,
      Nat.cast_one, one_mul] using h
  · simpa only [weightedSum, retainedSum, if_neg hdq] using h

theorem Jrho_split_source {N q : ℕ} [NeZero q] {x : ℝ}
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e) (eta : ℝ) :
    (∑ chi : Character q, CompleteExpansion.zeroValueSum chi N (x / q) eta) =
      (∑ chi : Character q, ∑ rho ∈ retainedValues chi (x / q) d e,
        (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta) +
          if d.modulus ∣ q then Jrho N e eta else 0 := by
  have h := sum_split_retained (q := q) (x / q) d e
    (fun chi rho => (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta)
  simp only [source_mem_iff hx hq hd, and_true] at h
  by_cases hdq : d.modulus ∣ q
  · simpa only [CompleteExpansion.zeroValueSum, zeroMultiplicity, if_pos hdq,
      show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from source_multiplicity hx hq hd hdq,
      Nat.cast_one, one_mul] using h
  · simpa only [CompleteExpansion.zeroValueSum, zeroMultiplicity, if_neg hdq] using h

end LiuWang.Proof.WeightedLowZeros
