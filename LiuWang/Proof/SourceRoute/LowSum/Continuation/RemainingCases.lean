import LiuWang.Proof.SourceRoute.LowSum.Continuation.RowIntegrals
import LiuWang.Proof.SourceRoute.LowSum.KOneCounts

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation

theorem family_two_zero_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (htwo : familyCount q (cap N 0.32) (omegaCutoff N q) ≤ 2)
    (hcap : ∀ (chi : Character q), ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      rho.re ≤ cap N (1 / 9.645908801)) :
    lowSum N q ≤ 0.0194 / sourceL N :=
  two_zero_original_from_counts hN hq (fun _ hi => family_nine_rows hN hq hi) htwo hcap

theorem full_counting_033_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    countingFunction (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q))
      zeroMultiplicity (cap N 0.33) ≤ 13 := by
  rw [countingFunction_full _ (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])]
  exact_mod_cast family_count_033 hN hq

theorem family_K1_small_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : ∀ alpha ∈ Set.Ioo (cap N 0.3221) (paperCap N),
      familyCount q alpha (omegaCutoff N q) ≤ 2) :
    (∫ alpha in cap N 0.33..paperCap N,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.0104 / sourceL N := by
  have h := original_K1_small_from_counts hN
    (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q))
    zeroMultiplicity (full_counting_033_paid hN hq)
    (fun alpha ha => by
      rw [countingFunction_full _ (by
        linarith [ha.1, cap_ge_098 hN (by norm_num : (0.3221 : ℝ) ≤ 0.478)])]
      exact_mod_cast h2 alpha ha)
  have hab : cap N 0.33 ≤ paperCap N := by
    apply (cap_order hN (by norm_num : (0.11 : ℝ) ≤ 0.33)).trans
    dsimp [cap, paperCap]
    linarith [paper_gap_le_low_gap hN]
  rw [full_integral_eq _ (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)]) hab] at h
  exact h

theorem family_K1_middle_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : ∀ alpha ∈ Set.Ioo (cap N 0.2743) (cap N 0.12),
      familyCount q alpha (omegaCutoff N q) ≤ 2) :
    (∫ alpha in cap N 0.33..cap N 0.12,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.0027 / sourceL N := by
  have h := original_K1_middle_from_counts hN
    (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q))
    zeroMultiplicity (full_counting_033_paid hN hq)
    (fun alpha ha => by
      rw [countingFunction_full _ (by
        linarith [ha.1, cap_ge_098 hN (by norm_num : (0.2743 : ℝ) ≤ 0.478)])]
      exact_mod_cast h2 alpha ha)
  rw [full_integral_eq _ (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num))] at h
  exact h

theorem family_K1_last_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h4 : ∀ alpha ∈ Set.Ioo (cap N 0.26213) (cap N 0.2067),
      familyCount q alpha (omegaCutoff N q) ≤ 4)
    (h2 : ∀ alpha ∈ Set.Ioo (cap N 0.2067) (cap N 0.15),
      familyCount q alpha (omegaCutoff N q) ≤ 2) :
    (∫ alpha in cap N 0.33..cap N 0.15,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 0.0001 / sourceL N := by
  have h := original_K1_last_from_counts hN
    (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q))
    zeroMultiplicity (full_counting_033_paid hN hq)
    (fun alpha ha => by
      rw [countingFunction_full _ (by
        linarith [ha.1, cap_ge_098 hN (by norm_num : (0.26213 : ℝ) ≤ 0.478)])]
      exact_mod_cast h4 alpha ha)
    (fun alpha ha => by
      rw [countingFunction_full _ (by
        linarith [ha.1, cap_ge_098 hN (by norm_num : (0.2067 : ℝ) ≤ 0.478)])]
      exact_mod_cast h2 alpha ha)
  rw [full_integral_eq _ (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num))] at h
  exact h

theorem full_integrand_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    (y : ℝ) {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun alpha => kernel N alpha * (familyCount q alpha y : ℝ)) volume a b := by
  have h := counting_integrand_integrable hN (by linarith : 0 < a) hab
    (fun chi : Character q => CompleteExpansion.zeroValues chi y) zeroMultiplicity
  apply h.congr
  intro alpha halpha
  rw [Set.uIoc_of_le hab] at halpha
  dsimp only
  rw [countingFunction_full y (ha.trans halpha.1.le)]

theorem family_reduction_at_033 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    lowSum N q ≤ 8.1e-10 / sourceL N + 3e-13 / sourceL N +
      ∫ alpha in cap N 0.33..1,
        kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ) := by
  have ha : 1 / 2 ≤ cap N 0.478 := by
    linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)]
  have hb : 1 / 2 ≤ cap N 0.33 := by
    linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)]
  have h := original_low_reduction hN hq
  change lowSum N q ≤ 8.1e-10 / sourceL N +
    ∫ alpha in cap N 0.478..1, kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ) at h
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (full_integrand_integrable (nat_pos_of_exp_le hN) _ ha (cap_order hN (by norm_num)))
    (full_integrand_integrable (nat_pos_of_exp_le hN) _ hb (cap_le_one hN (by norm_num))),
    ← add_assoc] at h
  exact h.trans (add_le_add (add_le_add le_rfl (family_first_eight_paid hN hq)) le_rfl)

end LiuWang.Proof.SourceRoute.LowSum.Continuation
