import LiuWang.Proof.SourceRoute.LowSum.Continuation.RemainingCases
import LiuWang.Proof.SourceRoute.Exception.Multiplicity

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart

def ClosedSlots (q : ℕ) [NeZero q] (alpha y : ℝ) :=
  {p : ZeroSlots q 0 y // alpha ≤ p.value.re}

instance closedSlotsFintype (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype (ClosedSlots q alpha y) :=
  inferInstanceAs (Fintype {p : ZeroSlots q 0 y // alpha ≤ p.value.re})

def closedSlotsEquiv (q : ℕ) [NeZero q] (alpha y : ℝ) :
    ClosedSlots q alpha y ≃
      Σ chi : Character q, Σ rho : {rho : ℂ // rho ∈ DirichletZeroCount.zeroValues chi alpha y},
        Fin (analyticOrderNatAt chi.LFunction rho.val) where
  toFun p := ⟨p.val.character, ⟨⟨p.val.value, by
    obtain ⟨hz, h0, _, h1, ht⟩ := mem_strictZeroValues.mp p.val.zero_mem
    exact DirichletZeroCount.mem_zeroValues.mpr ⟨hz, ⟨h0, h1, ht⟩, p.property⟩⟩,
    ⟨p.val.index, p.val.index_lt⟩⟩⟩
  invFun p := ⟨⟨p.1, p.2.1.val, p.2.2.val, by
    obtain ⟨hz, ⟨h0, h1, ht⟩, _⟩ := DirichletZeroCount.mem_zeroValues.mp p.2.1.property
    exact mem_strictZeroValues.mpr ⟨hz, h0, h0, h1, ht⟩,
    p.2.2.isLt⟩, (DirichletZeroCount.mem_zeroValues.mp p.2.1.property).2.2⟩
  left_inv p := by rcases p with ⟨⟨chi, rho, i, hr, hi⟩, ha⟩; rfl
  right_inv p := by rcases p with ⟨chi, ⟨⟨rho, hr⟩, ⟨i, hi⟩⟩⟩; rfl

theorem closedSlots_card (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype.card (ClosedSlots q alpha y) = familyCount q alpha y := by
  rw [Fintype.card_congr (closedSlotsEquiv q alpha y)]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_coe_sort, familyCount, count]

theorem familyCount_le_two_of_pair {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q 0 y)
    (hpair : ∀ r : ZeroSlots q 0 y, alpha ≤ r.value.re →
      r = p ∨ r = conjugateSlot p) :
    familyCount q alpha y ≤ 2 := by
  let f : ClosedSlots q alpha y → {r // r ∈ ({p, conjugateSlot p} : Finset _)} :=
    fun r => ⟨r.val, by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hpair r.val r.property⟩
  have hf : Function.Injective f := by
    intro r s he
    apply Subtype.ext
    exact congrArg (fun z : {r // r ∈ ({p, conjugateSlot p} : Finset _)} => z.val) he
  have h := Fintype.card_le_of_injective f hf
  rw [closedSlots_card, Fintype.card_coe] at h
  exact h.trans Finset.card_le_two

theorem low_cap_iff_lambda {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (a beta : ℝ) :
    cap N a ≤ beta ↔ (1 - beta) * Real.log (lowScale N) ≤ a := by
  have hlog : 0 < Real.log (lowScale N) := by
    linarith [show 25.3294 ≤ Real.log (lowScale N) from
      original_log_scale_lower (sourceL_ge_3100 hN)]
  rw [← le_div_iff₀ hlog]
  dsimp [cap]
  constructor <;> intro h <;> linarith

theorem table_closed_pair (row : GeneralTableRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (p r : ZeroSlots q 0 (omegaCutoff N q))
    (hp : cap N (generalTableFirst row) ≤ p.value.re)
    (hr : cap N (generalTableSecond row) ≤ r.value.re) :
    r = p ∨ r = conjugateSlot p := by
  by_contra hn
  have hne : p ≠ r := fun he => hn (Or.inl he.symm)
  have hnc : p ≠ conjugateSlot r := by
    intro he
    have h := congrArg conjugateSlot he
    rw [conjugateSlot_involutive] at h
    exact hn (Or.inr h.symm)
  obtain ⟨hx, hqx, _⟩ := Exception.low_scale_table_domain hN hq
  have h := ParentStrictTable.full_strip_strict row hx hqx p r hne hnc
    ((low_cap_iff_lambda hN _ _).mp hp)
  exact (not_lt_of_ge ((low_cap_iff_lambda hN _ _).mp hr)) h

theorem familyCount_table_of_seed (row : GeneralTableRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hp : cap N (generalTableFirst row) ≤ rho.re) {alpha : ℝ}
    (ha : cap N (generalTableSecond row) ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) ≤ 2 :=
  familyCount_le_two_of_pair (Exception.actualZeroSlot chi hr)
    (fun r h => table_closed_pair row hN hq _ r hp (ha.trans h))

theorem familyCount_03221_of_seed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hp : cap N 0.12 ≤ rho.re) {alpha : ℝ} (ha : cap N 0.3221 ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) ≤ 2 := by
  exact familyCount_table_of_seed .r12 hN hq hr
    (by simpa only [generalTableFirst, show (12 / 100 : ℝ) = 0.12 by norm_num] using hp)
    (by simpa only [generalTableSecond, show (3221 / 10000 : ℝ) = 0.3221 by norm_num] using ha)

theorem familyCount_02743_of_seed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hp : cap N 0.15 ≤ rho.re) {alpha : ℝ} (ha : cap N 0.2743 ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) ≤ 2 := by
  exact familyCount_table_of_seed .r15 hN hq hr
    (by simpa only [generalTableFirst, show (15 / 100 : ℝ) = 0.15 by norm_num] using hp)
    (by simpa only [generalTableSecond, show (2743 / 10000 : ℝ) = 0.2743 by norm_num] using ha)

theorem familyCount_02067 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha : ℝ} (ha : cap N 0.2067 ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) ≤ 2 := by
  by_cases hex : Nonempty (ClosedSlots q alpha (omegaCutoff N q))
  · obtain ⟨p⟩ := hex
    apply familyCount_le_two_of_pair p.val
    intro r hr
    apply table_closed_pair .r2067 hN hq p.val r
    · simpa only [generalTableFirst, show (2067 / 10000 : ℝ) = 0.2067 by norm_num]
        using ha.trans p.property
    · simpa only [generalTableSecond, show (2067 / 10000 : ℝ) = 0.2067 by norm_num]
        using ha.trans hr
  · have : IsEmpty (ClosedSlots q alpha (omegaCutoff N q)) := not_nonempty_iff.mp hex
    rw [← closedSlots_card, Fintype.card_of_isEmpty]
    norm_num

theorem cap_of_no_seed {N q : ℕ} [NeZero q] {a : ℝ}
    (hno : ¬ ∃ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) ∧ a ≤ rho.re) :
    ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      rho.re ≤ a := by
  intro chi rho hr
  exact (lt_of_not_ge (fun ha => hno ⟨chi, rho, hr, ha⟩)).le

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart
