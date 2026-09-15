import LiuWang.Proof.SourceRoute.Exception.PaperWindow

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.Exception

theorem slot_closed_cap_pair {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q 0 (x / q))
    (hl : (1 - p.value.re) * Real.log x ≤ 0.12)
    (hr : 1 - 0.3221 / Real.log x ≤ r.value.re) :
    r = p ∨ r = conjugateSlot p := by
  by_contra hn
  have hne : p ≠ r := by tauto
  have hnc : p ≠ conjugateSlot r := by
    intro he
    have hh := congrArg conjugateSlot he
    rw [conjugateSlot_involutive] at hh
    exact hn (Or.inr hh.symm)
  have h := ParentStrictTable.full_strip_strict .r12 hx hq p r hne hnc
    (by norm_num [generalTableFirst] at hl ⊢; exact hl)
  have hs : (0.3221 : ℝ) < (1 - r.value.re) * Real.log x := by
    simpa only [generalTableSecond, show (3221 / 10000 : ℝ) = 0.3221 by norm_num] using h
  have hlog : 0 < Real.log x := by linarith [source_log_lower hx]
  have hh := (div_lt_iff₀ hlog).mpr hs
  linarith

theorem closed_cap_slot_card_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p : ZeroSlots q 0 (x / q))
    (hl : (1 - p.value.re) * Real.log x ≤ 0.12) :
    (Finset.univ.filter (fun r : ZeroSlots q 0 (x / q) =>
      1 - 0.3221 / Real.log x ≤ r.value.re)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun r : ZeroSlots q 0 (x / q) =>
      1 - 0.3221 / Real.log x ≤ r.value.re) ⊆ {p, conjugateSlot p} := by
    intro r hr
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      slot_closed_cap_pair hx hq p r hl (Finset.mem_filter.mp hr).2
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem original_seed_closed_cap_counted_pair {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (p r : ZeroSlots q 0 (omegaCutoff N q))
    (he : 1 - 1 / (9.645908801 * Real.log (sourceP N)) ≤ p.value.re)
    (hr : cap N 0.3221 ≤ r.value.re) :
    r = p ∨ r = conjugateSlot p := by
  obtain ⟨hx, hqx, _⟩ := low_scale_table_domain hN hq
  have hl := original_seed_low_lambda hN he
  exact slot_closed_cap_pair hx hqx p r (hl.trans (by norm_num)) hr

theorem original_seed_closed_cap_multiplicity_le_two {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (p : ZeroSlots q 0 (omegaCutoff N q))
    (he : 1 - 1 / (9.645908801 * Real.log (sourceP N)) ≤ p.value.re) :
    (Finset.univ.filter (fun r : ZeroSlots q 0 (omegaCutoff N q) =>
      cap N 0.3221 ≤ r.value.re)).card ≤ 2 := by
  obtain ⟨hx, hqx, _⟩ := low_scale_table_domain hN hq
  have hl := original_seed_low_lambda hN he
  exact closed_cap_slot_card_le_two hx hqx p (hl.trans (by norm_num))

end LiuWang.Proof.SourceRoute.Exception
