import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5ActualPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem m5_below_gate_count_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) {y : ℝ}
    (hy : y ∈ Set.Icc (middleHeight N q) (sourceT N))
    (hyg : y ≤ max (100000 / (q : ℝ)) (10000 * Real.log q))
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (sourceCutoff q 0.478 (max (100000 / (q : ℝ)) (10000 * Real.log q))),
      (familyCount q alpha (max (100000 / (q : ℝ)) (10000 * Real.log q)) : ℝ) ≤
        sourceDensity q (max (100000 / (q : ℝ)) (10000 * Real.log q)) alpha) :
    countIntegral q N (max (100000 / (q : ℝ)) (10000 * Real.log q))
        (59 / 60) (sourceCutoff q 0.478 y) ≤
      600000 * Real.log ((q : ℝ) * y) ^ 6 *
        Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) := by
  have he : legalHeight q y = max (100000 / (q : ℝ)) (10000 * Real.log q) :=
    max_eq_right hyg
  have h := m5_legal_count_bound hN hq hq1 hy (by simpa only [he] using hdensity)
  simpa only [he] using h

theorem sourceM5_platform_and_bulk_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    let g := legalHeight q (middleHeight N q)
    (5 * N * Real.sqrt q / q.totient) *
      ((∫ y in middleHeight N q..g, y ^ (-2 : ℝ) *
          countIntegral q N y (59 / 60) (sourceCutoff q 0.478 y)) +
        ∫ y in g..sourceT N, y ^ (-2 : ℝ) *
          countIntegral q N y (59 / 60) (sourceCutoff q 0.478 y)) ≤
      0.00007 * (N : ℝ) / sourceL N := by
  dsimp only
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hg := ThirdDomainTail.source_high_gate_domain hN hq1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hi (u v : ℝ) (hu : lowHeight ≤ u) (huv : u ≤ v) :
      IntervalIntegrable (fun y => y ^ (-2 : ℝ) *
        countIntegral q N y (59 / 60) (sourceCutoff q 0.478 y)) volume u v := by
    simpa only [heightKernel, one_mul, show -(1 : ℝ) - 1 = -2 by norm_num] using
      heightKernel_mul_integrable (lowHeight_pos.trans_le hu) huv 1
        (moving_countIntegral_monotone hN hq hX hu huv
          (d := 0.478) (by norm_num) le_rfl).intervalIntegrable
  unfold legalHeight
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ hh.1 hg.1) (hi _ _ (hh.1.trans hg.1) hg.2.1)]
  exact sourceM5_original_paid hN hq hq1 hdensity htotient hnu

end LiuWang.Proof.Campaign20260915.ThirdBudgets
