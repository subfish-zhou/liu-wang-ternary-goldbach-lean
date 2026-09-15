import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Profiles
import LiuWang.Proof.MultiZeroRepulsion.Continuation.StrictTable

set_option autoImplicit false
noncomputable section

open scoped Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

def ClosedSlots (q : ℕ) [NeZero q] (alpha y : ℝ) :=
  Σ chi : DirichletCharacter ℂ q,
    Σ rho : {rho : ℂ // rho ∈ zeroValues chi alpha y},
      Fin (analyticOrderNatAt chi.LFunction rho.val)

instance closedSlotsFintype (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype (ClosedSlots q alpha y) := by unfold ClosedSlots; infer_instance

theorem card_closedSlots (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype.card (ClosedSlots q alpha y) = familyCount q alpha y := by
  simp only [ClosedSlots, Fintype.card_sigma, Fintype.card_fin, Finset.sum_coe_sort,
    familyCount, count]

def fullSlot {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ClosedSlots q alpha y) :
    ZeroSlots q 0 y where
  character := p.1
  value := p.2.1.val
  index := p.2.2.val
  zero_mem := by
    obtain ⟨hz, hstrip, _⟩ := mem_zeroValues.mp p.2.1.property
    exact mem_strictZeroValues.mpr ⟨hz, hstrip.1, hstrip.1, hstrip.2⟩
  index_lt := p.2.2.isLt

theorem fullSlot_injective {q : ℕ} [NeZero q] {alpha y : ℝ} :
    Function.Injective (@fullSlot q _ alpha y) := by
  rintro ⟨chi, ⟨⟨rho, hr⟩, k⟩⟩ ⟨psi, ⟨⟨tau, ht⟩, l⟩⟩ h
  have hc := congrArg ZeroSlots.character h
  have hv := congrArg ZeroSlots.value h
  have hi := congrArg ZeroSlots.index h
  dsimp [fullSlot] at hc hv hi
  subst psi
  subst tau
  have hk : k = l := Fin.ext hi
  subst l
  rfl

def gap {q : ℕ} [NeZero q] {y : ℝ} (p : ZeroSlots q 0 y) : ℝ :=
  (1 - p.value.re) * Real.log ((q : ℝ) * y)

def FirstCase (q : ℕ) [NeZero q] (y : ℝ) : Prop :=
  ∃ p : ZeroSlots q 0 y, gap p ≤ 0.12

def SecondCase (q : ℕ) [NeZero q] (y : ℝ) : Prop :=
  ∃ p : ZeroSlots q 0 y, 0.12 < gap p ∧ gap p ≤ 0.15

theorem gap_conjugate {q : ℕ} [NeZero q] {y : ℝ} (p : ZeroSlots q 0 y) :
    gap (conjugateSlot p) = gap p := rfl

theorem closedSlot_gap_le {q : ℕ} [NeZero q] {y lam : ℝ}
    (hs : 0 < Real.log ((q : ℝ) * y))
    (p : ClosedSlots q (1 - lam / Real.log ((q : ℝ) * y)) y) :
    gap (fullSlot p) ≤ lam := by
  have h := (mem_zeroValues.mp p.2.1.property).2.2
  have hh : 1 - p.2.1.val.re ≤ lam / Real.log ((q : ℝ) * y) := by linarith
  exact (le_div_iff₀ hs).mp hh

theorem original_strict_table (row : GeneralTableRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y)
    (p r : ZeroSlots q 0 y) (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hp : gap p ≤ generalTableFirst row) :
    generalTableSecond row < gap r := by
  have hd := original_table_domain hN hq hy
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have he : (q : ℝ) * y / q = y := mul_div_cancel_left₀ y hq0
  have hqx : (q : ℝ) ≤ (q : ℝ) * y := by
    simpa using mul_le_mul_of_nonneg_left hd.1 (Nat.cast_nonneg q)
  have ht := ParentStrictTable.full_strip_strict row
    (show (8000000000 : ℝ) ≤ (q : ℝ) * y by linarith [hd.2.1]) hqx
  rw [he] at ht
  exact ht p r hne hnc hp

theorem table_closed_count (row : GeneralTableRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y lam : ℝ} (hy : omegaCutoff N q ≤ y)
    (p : ZeroSlots q 0 y) (hp : gap p ≤ generalTableFirst row)
    (hlam : lam ≤ generalTableSecond row) :
    familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y ≤ 2 := by
  let A := ClosedSlots q (1 - lam / Real.log ((q : ℝ) * y)) y
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  have hm (r : A) : fullSlot r ∈ ({p, conjugateSlot p} : Finset _) := by
    by_contra hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hnc : p ≠ conjugateSlot (fullSlot r) := by
      intro he
      have hh := congrArg conjugateSlot he
      rw [conjugateSlot_involutive] at hh
      exact hn.2 hh.symm
    have ht := original_strict_table row hN hq hy p (fullSlot r) (Ne.symm hn.1) hnc hp
    have hr := closedSlot_gap_le hs r
    linarith
  let f : A → {r // r ∈ ({p, conjugateSlot p} : Finset _)} :=
    fun r => ⟨fullSlot r, hm r⟩
  have hf : Function.Injective f := fun _ _ h => fullSlot_injective (congrArg Subtype.val h)
  have hh := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hh
  exact (card_closedSlots q _ _).symm.trans_le (hh.trans Finset.card_le_two)

theorem actual_first_count {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y lam : ℝ} (hy : omegaCutoff N q ≤ y) (hc : FirstCase q y) (hlam : lam ≤ 0.3221) :
    familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y ≤ 2 := by
  obtain ⟨p, hp⟩ := hc
  apply table_closed_count .r12 hN hq hy p
  · simpa only [generalTableFirst] using (show gap p ≤ 12 / 100 by norm_num at hp ⊢; exact hp)
  · norm_num [generalTableSecond] at *
    exact hlam

theorem actual_second_count {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y lam : ℝ} (hy : omegaCutoff N q ≤ y) (hc : SecondCase q y) (hlam : lam ≤ 0.2743) :
    familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y ≤ 2 := by
  obtain ⟨p, _, hp⟩ := hc
  apply table_closed_count .r15 hN hq hy p
  · norm_num [generalTableFirst] at *
    exact hp
  · norm_num [generalTableSecond] at *
    exact hlam

theorem actual_second_exclusion {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y lam : ℝ} (hy : omegaCutoff N q ≤ y) (hc : SecondCase q y) (hlam : lam ≤ 0.12) :
    familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y = 0 := by
  obtain ⟨p, hp0, hp⟩ := hc
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  have he : IsEmpty (ClosedSlots q (1 - lam / Real.log ((q : ℝ) * y)) y) := ⟨by
    intro r
    have hr := closedSlot_gap_le hs r
    have hne : p ≠ fullSlot r := by intro h; rw [← h] at hr; linarith
    have hnc : p ≠ conjugateSlot (fullSlot r) := by
      intro h
      have hg := congrArg gap h
      rw [gap_conjugate] at hg
      linarith
    have ht := original_strict_table .r15 hN hq hy p (fullSlot r) hne hnc
      (by norm_num [generalTableFirst] at *; exact hp)
    norm_num [generalTableSecond] at ht
    linarith⟩
  rw [← card_closedSlots, Fintype.card_of_isEmpty]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
