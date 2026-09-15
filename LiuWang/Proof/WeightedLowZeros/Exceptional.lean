import LiuWang.Proof.WeightedLowZeros.Main
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Consumer

/-!
# A common actual R24 source before any deletion

This is the integrated R24 region, not the wider source R9.645908801 region.
The source predicate contains only an actual primitive L zero and its location.
At the low-height scale we use `x = 3.36 P`, not `P` or `P1`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros

def regionCap (x : ℝ) : ℝ := 1 - 1 / (24 * Real.log x)

def SourceAt (x : ℝ) (d : PrimitiveQuadraticDatum) (e : ℂ) : Prop :=
  (d.modulus : ℝ) ≤ x ∧ datumL d e = 0 ∧ e.im = 0 ∧ e.re < 1 ∧ regionCap x < e.re

def retainedValues {q : ℕ} [NeZero q] (chi : Character q) (y : ℝ)
    (d : PrimitiveQuadraticDatum) (e : ℂ) : Finset ℂ :=
  (CompleteExpansion.zeroValues chi y).filter (fun rho => chi ≠ inducedAt d q ∨ rho ≠ e)

def retainedSum (N q : ℕ) [NeZero q] (y : ℝ)
    (d : PrimitiveQuadraticDatum) (e : ℂ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ retainedValues chi y d e,
    (zeroMultiplicity chi rho : ℝ) * weight N rho.re

theorem regionCap_pos {x : ℝ} (hx : 10 ≤ x) : 0 < regionCap x := by
  have hl : 1 < Real.log x := by
    apply (Real.lt_log_iff_exp_lt (by linarith)).mpr
    linarith [Real.exp_one_lt_d9]
  have hw : 1 / (24 * Real.log x) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  dsimp [regionCap]
  linarith

theorem source_controls {x : ℝ} (hx : 10 ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e) :
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ x →
      ∀ (chi : Character q) (rho : ℂ), RealClosure.region x q rho →
        (chi ≠ 1 ∨ rho ≠ 1) → chi.LFunction rho = 0 →
          rho = e ∧ d.modulus = chi.conductor ∧ d.modulus ∣ q ∧
            inducedAt d q = chi ∧ zeroMultiplicity chi rho = 1 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hr : RealClosure.region x d.modulus e :=
    ⟨hd.2.2.2.2, by rw [hd.2.2.1, abs_zero]; positivity⟩
  obtain ⟨d', hd', _, _, hz', _, _, hall⟩ := RealClosure.family_fixed_source
    hx hd.1 d.character hr (Or.inl d.ne_one) hd.2.1
  have he : (e.re : ℂ) = e := by apply Complex.ext <;> simp [hd.2.2.1]
  have hb : 0 < e.re := (regionCap_pos hx).trans hd.2.2.2.2
  have hdd : d' = d := real_sources_unique d' d hx hd' hd.1 hb hb
    (by simpa only [he] using hz') (by simpa only [he] using hd.2.1)
    (by linarith [hr.1]) (by linarith [hr.1])
  subst d'
  exact hall

theorem exists_source_of_mem {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (x / q))
    (hcap : regionCap x < rho.re) :
    ∃ d : PrimitiveQuadraticDatum, SourceAt x d rho := by
  obtain ⟨hz, _, h1, hy, _⟩ := CompleteExpansion.mem_zeroValues.mp hr
  have hp : chi ≠ 1 ∨ rho ≠ 1 :=
    Or.inr (fun he => by simp [he] at h1)
  obtain ⟨d, hd, _, _, hdz, hi, _, _⟩ :=
    RealClosure.family_fixed_source hx hq chi ⟨hcap, hy⟩ hp hz
  exact ⟨d, hd, hdz, hi, h1, hcap⟩

theorem retained_re_le {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e)
    (chi : Character q) {rho : ℂ} (hr : rho ∈ retainedValues chi (x / q) d e) :
    rho.re ≤ regionCap x := by
  obtain ⟨hr, hret⟩ := Finset.mem_filter.mp hr
  obtain ⟨hz, _, h1, hy, _⟩ := CompleteExpansion.mem_zeroValues.mp hr
  by_contra hcap
  have hp : chi ≠ 1 ∨ rho ≠ 1 :=
    Or.inr (fun he => by simp [he] at h1)
  obtain ⟨he, _, _, hc, _⟩ := source_controls hx hd q hq chi rho ⟨lt_of_not_ge hcap, hy⟩ hp hz
  exact hret.elim (fun h => h hc.symm) (fun h => h he)

theorem retainedSum_le {N q : ℕ} [NeZero q] {x a : ℝ}
    (hN : 1000 ≤ (N : ℝ)) (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (ha : 0 < a)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt x d e) :
    retainedSum N q (x / q) d e ≤ weight N (regionCap x) * countMother q (x / q) a := by
  unfold retainedSum countMother
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro chi _
  exact subset_weighted_le hN chi (by positivity) ha (regionCap_pos hx)
    (retainedValues chi (x / q) d e) (Finset.filter_subset _ _)
    (fun _ hr => retained_re_le hx hq hd chi hr)

theorem no_source_weightedSum_le {N q : ℕ} [NeZero q] {x a : ℝ}
    (hN : 1000 ≤ (N : ℝ)) (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (ha : 0 < a)
    (hnone : ¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), SourceAt x d e)
    (chi : Character q) :
    weightedSum N chi (x / q) ≤
      weight N (regionCap x) * DirichletZeroCount.sharpenedBound chi (x / q) a := by
  apply subset_weighted_le hN chi (by positivity) ha (regionCap_pos hx)
    (CompleteExpansion.zeroValues chi (x / q)) (fun _ h => h)
  intro rho hr
  by_contra hc
  obtain ⟨d, hd⟩ := exists_source_of_mem hx hq hr (lt_of_not_ge hc)
  exact hnone ⟨d, rho, hd⟩

def lowScale (N : ℕ) : ℝ := 3.36 * sourceP N

theorem lowScale_parameters {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    10 ≤ lowScale N ∧ (q : ℝ) ≤ lowScale N ∧
      lowScale N / q = omegaCutoff N q := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hP : 8 ≤ sourceP N := by
    exact (by norm_num : (8 : ℝ) = 2 ^ (3 : ℕ)) ▸
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ sourceL N) 3
  dsimp [lowScale]
  exact ⟨by linarith, by linarith, rfl⟩

theorem common_source_low_dichotomy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) {a : ℝ} (ha : 0 < a) :
    ((¬ ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), SourceAt (lowScale N) d e) ∧
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
        lowSum N q ≤ weight N (regionCap (lowScale N)) *
          countMother q (omegaCutoff N q) a) ∨
    (∃ (d : PrimitiveQuadraticDatum) (e : ℂ), SourceAt (lowScale N) d e ∧
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
        retainedSum N q (omegaCutoff N q) d e ≤
          weight N (regionCap (lowScale N)) * countMother q (omegaCutoff N q) a) := by
  by_cases hex : ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), SourceAt (lowScale N) d e
  · obtain ⟨d, e, hd⟩ := hex
    refine Or.inr ⟨d, e, hd, ?_⟩
    intro q _ hq
    obtain ⟨hx, hqx, he⟩ := lowScale_parameters hN hq
    simpa only [he] using retainedSum_le (source_endpoint_ge_thousand hN) hx hqx ha hd
  · refine Or.inl ⟨hex, ?_⟩
    intro q _ hq
    obtain ⟨hx, hqx, he⟩ := lowScale_parameters hN hq
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
      (fun chi _ => no_source_weightedSum_le (source_endpoint_ge_thousand hN) hx hqx ha hex chi)
    simpa only [he, ← Finset.mul_sum, lowSum, countMother] using h

end LiuWang.Proof.WeightedLowZeros
