import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceFreeFamily
import LiuWang.Proof.Campaign20260915.OriginalRegion.LowWeight
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.RealTail

/-! Actual paper-scale consumers; the scale lower bound is proved, not added as a premise. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.LowSum
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem sourceP_original_scale {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    8000000000 ≤ sourceP N := by
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) (sourceL_ge_3100 hN) 3
  change 8000000000 ≤ sourceL N ^ 3
  norm_num at hh
  linarith

theorem moving_original_real {q : ℕ} [NeZero q] {y : ℝ}
    (hx : 8000000000 ≤ (q : ℝ) * y) (hy : 1 ≤ y)
    (chi : Character q) (rho : ℂ) (hz : chi.LFunction rho = 0)
    (hr1 : rho.re < 1) (ht : |rho.im| ≤ y)
    (hr : 1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re) : rho.im = 0 := by
  have hq : (q : ℝ) ≤ (q : ℝ) * y := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg q)
  have he : (q : ℝ) * y / q = y := by
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
    field_simp
  exact (source_free_original_classification hx hq chi hr hr1 (by simpa only [he] using ht) hz).2.2.1

theorem original_high_local_source_free {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N), ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0 := by
  intro y hy chi rho hz _hr0 hr1 ht hr
  have hlow := (original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).1.trans hy.1
  exact moving_original_real (by linarith [(M3_table_domain hN hq hlow).1])
    (lowHeight_ge_one.trans hlow) chi rho hz hr1 ht hr

theorem equation_5_42_source_free {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (5 * N * Real.sqrt q / q.totient) *
      (∫ y in middleHeight N q..sourceT N, y ^ (-2 : ℝ) *
        countIntegral q N y (59 / 60) 1) =
      sourceM5 N q + sourceM6 N q + sourceHighRealTail N q :=
  equation_5_42_with_real_tail hN hq hq1 (original_high_local_source_free hN hq hq1)

theorem original_middle_local_source_free {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0 := by
  intro chi rho hz _hr0 hr1 ht hr
  have hy1 : 1 ≤ y := by linarith [SourceRoute.LowSum.Continuation.low_height_ge hq]
  have hmul := mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg q)
  rw [SourceRoute.LowSum.Continuation.omega_eq_lowScale_div, mul_div_cancel₀ _
    (show (q : ℝ) ≠ 0 by exact_mod_cast NeZero.ne q)] at hmul
  exact moving_original_real
    (by linarith [SourceRoute.LowSum.Continuation.lowScale_effective hN])
    hy1 chi rho hz hr1 ht hr

theorem source_free_nonreal_seed_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hi : rho.im ≠ 0) : rho.re ≤ cap N (1 / 9.645908801) := by
  have hm := CompleteExpansion.mem_zeroValues.mp hr
  have hp : sourceP N ≤ lowScale N := by
    have hpos := (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le
    change sourceP N ≤ 3.36 * sourceP N
    linarith
  by_contra hh
  have hb : 1 - 1 / (9.645908801 * Real.log (lowScale N)) < rho.re := by
    simpa only [cap, div_div] using lt_of_not_ge hh
  exact hi (source_free_original_classification
    (by linarith [SourceRoute.LowSum.Continuation.lowScale_effective hN])
    (hq.trans hp) chi hb hm.2.2.1 hm.2.2.2.1 hm.1).2.2.1

theorem low_sum_of_short_absence_source_free {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N) :
    lowSum N q ≤ 0.0194 / sourceL N :=
  SourceRoute.LowSum.Continuation.Restart.original_low_sum_of_short_absence hN hq hshort
    (fun _ _ hr _ hi => source_free_nonreal_seed_cap hN hq hr hi)

theorem low_weight_of_short_absence_source_free {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : ∀ chi : Character q, ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      |rho.im| ≤ sourceP N / q → rho.re < paperCap N) :
    SourceRoute.MajorOrdinary.lowWeightSum N q ≤ 0.0194 / sourceL N := by
  rw [lowWeightSum_eq_lowSum hN]
  exact low_sum_of_short_absence_source_free hN hq hshort

theorem original_short_classification_closed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (ht : |rho.im| ≤ sourceP N / q) (hb : paperCap N ≤ rho.re) :
    chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 := by
  have hm := CompleteExpansion.mem_zeroValues.mp hr
  exact source_free_original_classification_closed (sourceP_original_scale hN) hq chi
    hb hm.2.2.1 ht hm.1

end LiuWang.Proof.Campaign20260915.OriginalRegion
