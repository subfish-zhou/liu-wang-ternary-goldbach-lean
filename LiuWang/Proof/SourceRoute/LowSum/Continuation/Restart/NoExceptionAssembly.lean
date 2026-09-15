import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.KOneExhaustion

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart

theorem actual_pair_of_seed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi psi : Character q} {rho tau : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (ht : tau ∈ CompleteExpansion.zeroValues psi (omegaCutoff N q))
    (hp : cap N 0.12 ≤ rho.re) (ha : cap N 0.3221 ≤ tau.re) :
    (psi = chi ∧ tau = rho) ∨ (psi = chi⁻¹ ∧ tau = conj rho) := by
  have h := table_closed_pair .r12 hN hq
    (Exception.actualZeroSlot chi hr) (Exception.actualZeroSlot psi ht)
    (by simpa only [Exception.actualZeroSlot, generalTableFirst,
      show (12 / 100 : ℝ) = 0.12 by norm_num] using hp)
    (by simpa only [Exception.actualZeroSlot, generalTableSecond,
      show (3221 / 10000 : ℝ) = 0.3221 by norm_num] using ha)
  rcases h with he | he
  · exact Or.inl ⟨congrArg ZeroSlots.character he, congrArg ZeroSlots.value he⟩
  · exact Or.inr ⟨congrArg ZeroSlots.character he, congrArg ZeroSlots.value he⟩

theorem all_zero_cap_of_seed_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hp : cap N 0.12 ≤ rho.re)
    (hc : rho.re ≤ cap N (1 / 9.645908801)) :
    ∀ psi : Character q, ∀ tau ∈ CompleteExpansion.zeroValues psi (omegaCutoff N q),
      tau.re ≤ cap N (1 / 9.645908801) := by
  intro psi tau ht
  by_cases ha : cap N 0.3221 ≤ tau.re
  · rcases actual_pair_of_seed hN hq hr ht hp ha with ⟨_, he⟩ | ⟨_, he⟩
    · simpa only [he] using hc
    · simpa only [he, Complex.conj_re] using hc
  · exact (le_of_not_ge ha).trans (cap_order hN (by norm_num))

theorem family_tail_of_seed_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hp : cap N 0.12 ≤ rho.re)
    (hc : rho.re ≤ cap N (1 / 9.645908801)) :
    (∫ alpha in bulkCap N..1,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.01938 / sourceL N := by
  let Z := fun psi : Character q => CompleteExpansion.zeroValues psi (omegaCutoff N q)
  have ht := original_two_zero_tail hN Z zeroMultiplicity
    (fun i hi => subset_nine_rows hN hq Z (fun _ _ h => h) hi)
    (by
      rw [countingFunction_full _ (by linarith [cap_ge_098 hN (by norm_num : (0.32 : ℝ) ≤ 0.478)])]
      exact_mod_cast familyCount_03221_of_seed hN hq hr hp (cap_order hN (by norm_num)))
    (all_zero_cap_of_seed_cap hN hq hr hp hc)
  change (∫ alpha in cap N 0.478..1, kernel N alpha * countingFunction Z zeroMultiplicity alpha) ≤ _ at ht
  rw [full_integral_eq _ (by linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)])
    (cap_le_one hN (by norm_num))] at ht
  exact ht

theorem family_tail_exhaustive {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hc1 : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      paperCap N ≤ rho.re → rho.re ≤ cap N (1 / 9.645908801)) :
    (∫ alpha in bulkCap N..1,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.01938 / sourceL N := by
  by_cases hex : ∃ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) ∧ paperCap N ≤ rho.re
  · obtain ⟨chi, rho, hr, hp⟩ := hex
    exact family_tail_of_seed_cap hN hq hr
      (((cap_order hN (by norm_num : (0.11 : ℝ) ≤ 0.12)).trans (cap_011_le_paper hN)).trans hp)
      (hc1 chi rho hr hp)
  · exact (family_tail_of_paper_cap hN hq (cap_of_no_seed hex)).trans
      (div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN]))

theorem original_low_sum_exhaustive {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hc1 : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      paperCap N ≤ rho.re → rho.re ≤ cap N (1 / 9.645908801)) :
    lowSum N q ≤ 0.0194 / sourceL N := by
  have h := (original_low_reduction hN hq).trans
    (add_le_add le_rfl (family_tail_exhaustive hN hq hc1))
  apply h.trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN])

theorem original_high_seed_nonreal {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hshort : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hp : paperCap N ≤ rho.re) :
    sourceP N / q < |rho.im| ∧ rho.im ≠ 0 := by
  have ht : sourceP N / q < |rho.im| := lt_of_not_ge (fun h => (not_lt_of_ge hp) (hshort chi rho hr h))
  have hP : 0 ≤ sourceP N := (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le
  refine ⟨ht, ?_⟩
  intro he
  rw [he, abs_zero] at ht
  exact (not_lt_of_ge (div_nonneg hP (Nat.cast_nonneg q))) ht

theorem original_low_sum_of_short_absence {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N)
    (hcomplex : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      paperCap N ≤ rho.re → rho.im ≠ 0 → rho.re ≤ cap N (1 / 9.645908801)) :
    lowSum N q ≤ 0.0194 / sourceL N :=
  original_low_sum_exhaustive hN hq (fun chi rho hr hp =>
    hcomplex chi rho hr hp (original_high_seed_nonreal hN hshort hr hp).2)

theorem original_full_Jrho_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hc1 : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      paperCap N ≤ rho.re → rho.re ≤ cap N (1 / 9.645908801)) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
        (N : ℝ) * (0.0194 / sourceL N) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => subset_Jrho_le (nat_pos_of_exp_le hN) chi (omegaCutoff N q) eta
      (CompleteExpansion.zeroValues chi (omegaCutoff N q)) (fun _ hr => hr))
  rw [← Finset.mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_left (original_low_sum_exhaustive hN hq hc1) (Nat.cast_nonneg _))

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart
