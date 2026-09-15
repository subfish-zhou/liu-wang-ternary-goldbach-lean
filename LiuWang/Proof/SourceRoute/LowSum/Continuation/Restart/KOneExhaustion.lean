import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.ClosedCounts

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart

theorem family_integral_truncate {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {a c b : ℝ}
    (ha : 1 / 2 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
    (hcap : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      rho.re ≤ c) :
    (∫ alpha in a..b, kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) =
      ∫ alpha in a..c, kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ) := by
  rw [← full_integral_eq _ ha (hac.trans hcb), ← full_integral_eq _ ha hac]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable (nat_pos_of_exp_le hN) (by linarith) hac _ zeroMultiplicity)
    (counting_integrand_integrable (nat_pos_of_exp_le hN) (by linarith) hcb _ zeroMultiplicity),
    counting_integral_zero_above_cap N _ zeroMultiplicity hcb hcap, add_zero]

theorem cap_011_le_paper {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    cap N 0.11 ≤ paperCap N := by
  dsimp [cap, paperCap]
  linarith [paper_gap_le_low_gap hN]

theorem paper_cap_le_one {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    paperCap N ≤ 1 := by
  have hP : 1 ≤ sourceP N := one_le_sourceP (exp_2000_le_of_exp_3100_le hN)
  have hlog := Real.log_nonneg hP
  dsimp [paperCap]
  have : 0 ≤ 1 / (9.645908801 * Real.log (sourceP N)) := by positivity
  linarith

theorem original_last_integrals_with_thirteen {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.33..cap N 0.26213, 13 * kernel N alpha) +
      (∫ alpha in cap N 0.26213..cap N 0.2067, 13 * kernel N alpha) +
      (∫ alpha in cap N 0.2067..cap N 0.15, 2 * kernel N alpha) ≤ 0.0001 / sourceL N := by
  have h1 : (∫ alpha in cap N 0.33..cap N 0.26213, 13 * kernel N alpha) ≤
      4.8e-10 / sourceL N := by
    apply small_segment_paid hN seed_026213.2 seed_033.1 <;> norm_num
  have h2 : (∫ alpha in cap N 0.26213..cap N 0.2067, 13 * kernel N alpha) ≤
      4.225e-7 / sourceL N := by
    apply small_segment_paid hN seed_02067.2 seed_026213.1 <;> norm_num
  have h3 : (∫ alpha in cap N 0.2067..cap N 0.15, 2 * kernel N alpha) ≤
      0.000067 / sourceL N := by
    apply small_segment_paid hN seed_015.2 seed_02067.1 <;> norm_num
  apply (add_le_add (add_le_add h1 h2) h3).trans
  rw [← add_div, ← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN])

theorem family_K1_last_actual {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in cap N 0.33..cap N 0.15,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.0001 / sourceL N := by
  let Z := fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q)
  have hpos : 0 < cap N 0.33 := by
    linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)]
  have hmid : 0 < cap N 0.2067 := by
    linarith [cap_ge_098 hN (by norm_num : (0.2067 : ℝ) ≤ 0.478)]
  have h13 : ∀ alpha, cap N 0.33 ≤ alpha → countingFunction Z zeroMultiplicity alpha ≤ 13 :=
    fun _ ha => (countingFunction_antitone Z zeroMultiplicity ha).trans (full_counting_033_paid hN hq)
  have hi := counting_integral_two_pieces (nat_pos_of_exp_le hN) Z zeroMultiplicity hpos
    (cap_order hN (by norm_num : (0.26213 : ℝ) ≤ 0.33))
    (cap_order hN (by norm_num : (0.2067 : ℝ) ≤ 0.26213))
    (fun _ ha => h13 _ ha.1.le)
    (fun _ ha => h13 _ ((cap_order hN (by norm_num : (0.26213 : ℝ) ≤ 0.33)).trans ha.1.le))
  have hj := counting_integral_le_open (nat_pos_of_exp_le hN) Z zeroMultiplicity hmid
    (cap_order hN (by norm_num : (0.15 : ℝ) ≤ 0.2067))
    (D := 2) (fun alpha ha => by
      rw [countingFunction_full _ (by
        linarith [ha.1, cap_ge_098 hN (by norm_num : (0.2067 : ℝ) ≤ 0.478)])]
      exact_mod_cast familyCount_02067 hN hq ha.1.le)
  have hh := (add_le_add hi hj).trans (original_last_integrals_with_thirteen hN)
  rw [intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable (nat_pos_of_exp_le hN) hpos
      (cap_order hN (by norm_num)) Z zeroMultiplicity)
    (counting_integrand_integrable (nat_pos_of_exp_le hN) hmid
      (cap_order hN (by norm_num)) Z zeroMultiplicity)] at hh
  rw [full_integral_eq _ (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num))] at hh
  exact hh

theorem family_K1_exhaustive {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in cap N 0.33..paperCap N,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.0104 / sourceL N := by
  by_cases h12 : ∃ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) ∧ cap N 0.12 ≤ rho.re
  · obtain ⟨chi, rho, hr, hp⟩ := h12
    exact family_K1_small_paid hN hq
      (fun _ ha => familyCount_03221_of_seed hN hq hr hp ha.1.le)
  · have hc12 := cap_of_no_seed h12
    by_cases h15 : ∃ (chi : Character q) (rho : ℂ),
        rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) ∧ cap N 0.15 ≤ rho.re
    · obtain ⟨chi, rho, hr, hp⟩ := h15
      rw [family_integral_truncate hN
        (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
        (cap_order hN (by norm_num : (0.12 : ℝ) ≤ 0.33))
        ((cap_order hN (by norm_num : (0.11 : ℝ) ≤ 0.12)).trans (cap_011_le_paper hN)) hc12]
      exact (family_K1_middle_paid hN hq
        (fun _ ha => familyCount_02743_of_seed hN hq hr hp ha.1.le)).trans
          (div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN]))
    · have hc15 := cap_of_no_seed h15
      rw [family_integral_truncate hN
        (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
        (cap_order hN (by norm_num : (0.15 : ℝ) ≤ 0.33))
        ((cap_order hN (by norm_num : (0.11 : ℝ) ≤ 0.15)).trans (cap_011_le_paper hN)) hc15]
      exact (family_K1_last_actual hN hq).trans
        (div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN]))

theorem family_tail_of_paper_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hpaper : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      rho.re ≤ paperCap N) :
    (∫ alpha in bulkCap N..1,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.0105 / sourceL N := by
  have ha : 1 / 2 ≤ cap N 0.478 := by
    linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)]
  have hb : 1 / 2 ≤ cap N 0.33 := by
    linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)]
  change (∫ alpha in cap N 0.478..1, kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (full_integrand_integrable (nat_pos_of_exp_le hN) _ ha (cap_order hN (by norm_num)))
    (full_integrand_integrable (nat_pos_of_exp_le hN) _ hb (cap_le_one hN (by norm_num))),
    family_integral_truncate hN hb
      ((cap_order hN (by norm_num : (0.11 : ℝ) ≤ 0.33)).trans (cap_011_le_paper hN))
      (paper_cap_le_one hN) hpaper]
  apply (add_le_add (family_first_eight_paid hN hq) (family_K1_exhaustive hN hq)).trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN])

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart
