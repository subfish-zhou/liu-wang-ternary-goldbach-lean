import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OrdinaryBands
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.LowerBeta
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.HighEndpoint
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.Principal

/-! The original ordinary-count portions of Sigma5 and Sigma6 are paid on the actual zero sums. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem scaled_low_beta_le {q : ℕ} [NeZero q] {X u v p c C : ℝ}
    (hX : 1 ≤ X)
    (hband : ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) (59 / 60), c * densityBand q alpha u v p ≤ C) :
    c * (X ^ (-1 / 2 : ℝ) * densityBand q (1 / 2) u v p +
      ∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel X alpha * densityBand q alpha u v p) ≤
        C * (X ^ (-1 / 2 : ℝ) + ∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel X alpha) := by
  have hx : 0 < X := by linarith
  have hp := mul_le_mul_of_nonneg_left (hband (1 / 2) ⟨le_rfl, by norm_num⟩)
    (Real.rpow_nonneg hx.le (-1 / 2 : ℝ))
  have hi : c * (∫ alpha in (1 / 2 : ℝ)..(59 / 60),
      betaKernel X alpha * densityBand q alpha u v p) ≤
        C * (∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel X alpha) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 59 / 60)
      ((densityBand_beta_integrable q u v p hx (a := 1 / 2) (b := 59 / 60)
        le_rfl (by norm_num)).const_mul _)
      (((betaKernel_continuous hx).const_mul _).intervalIntegrable _ _)
    intro alpha halpha
    have hk : 0 ≤ betaKernel X alpha :=
      mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg hX)
    have h := mul_le_mul_of_nonneg_left (hband alpha halpha) hk
    nlinarith only [h]
  nlinarith only [hp, hi]

theorem sigma5_low_beta_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sigma5 N q ≤ 0.0011 * (N : ℝ) / sourceL N +
      (16 * N * Real.sqrt q / q.totient) *
        ∫ alpha in (59 / 60 : ℝ)..1, betaKernel (0.001 * N) alpha *
          densityBand q alpha lowHeight (middleHeight N q) (1 / 2) := by
  have h := scaled_low_beta_le (q := q) (original_middle_base_ge_one hN)
    (fun alpha halpha => original_middle_ordinary_band hN hq1 (show 0 ≤ alpha by linarith [halpha.1]))
  have hp := mul_le_mul_of_nonneg_left h (show 0 ≤ 16 * (N : ℝ) by positivity)
  have he := equation_5_30_integral hN
  rw [equation_5_28 (exp_2000_le_of_exp_3100_le hN) hq1]
  ring_nf at hp he ⊢
  linarith only [hp, he]

theorem sigma6_low_beta_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sigma6 N q ≤ 0.00012 * (N : ℝ) / sourceL N +
      (5 * N * Real.sqrt q / q.totient) *
        ∫ alpha in (59 / 60 : ℝ)..1, betaKernel N alpha *
          densityBand q alpha (middleHeight N q) (sourceT N) 1 := by
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have h := scaled_low_beta_le (q := q) (c := 1) hX
    (fun alpha halpha => by
      simpa only [one_mul] using original_high_ordinary_band hN hq1
        (show 0 ≤ alpha by linarith [halpha.1]))
  have hf : (q.totient : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)) : (0 : ℝ) < q.totient).ne'
  have hp := mul_le_mul_of_nonneg_left h
    (show 0 ≤ 5 * N * Real.sqrt q / q.totient by positivity)
  have he := equation_5_40_low_integral hN hq1
  have hcancel : (5 * N * Real.sqrt q / q.totient) *
      (101 * q.totient * Real.log (sourceL N) ^ 2 *
        ((N : ℝ) ^ (-1 / 2 : ℝ) + ∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel N alpha)) =
      505 * N * Real.sqrt q * Real.log (sourceL N) ^ 2 *
        ((N : ℝ) ^ (-1 / 2 : ℝ) + ∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel N alpha) := by
    field_simp
    ring
  rw [hcancel] at hp
  rw [equation_5_38 (exp_2000_le_of_exp_3100_le hN)]
  ring_nf at hp he ⊢
  linarith only [hp, he]

theorem equation_5_31_actual_count {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sigma5 N q ≤ 0.0011 * (N : ℝ) / sourceL N +
      (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1 +
      (8 * N * Real.sqrt q / q.totient) *
        ∫ y in lowHeight..middleHeight N q,
          y ^ (-3 / 2 : ℝ) * countIntegral q (0.001 * N) y (59 / 60) 1 := by
  have hp := sigma5_low_beta_paid hN hq1
  have h := mul_le_mul_of_nonneg_left (original_middle_count_reduction hN hq1)
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient by positivity)
  ring_nf at hp h ⊢
  linarith only [hp, h]

theorem sigma6_low_and_endpoint_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : (DirichletZeroCount.familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60)) :
    sigma6 N q ≤ (0.00012 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
      (5 * N * Real.sqrt q / q.totient) *
        ∫ y in middleHeight N q..sourceT N,
          y ^ (-2 : ℝ) * countIntegral q N y (59 / 60) 1 := by
  have h := sigma6_low_beta_paid hN hq1
  have hp := high_count_reduction_endpoint_paid hN hq hq1 hdensity
  ring_nf at h hp ⊢
  linarith only [h, hp]

theorem S_four_new_payments {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N))
    (hlow : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (DirichletZeroCount.familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha)
    (hhigh : (DirichletZeroCount.familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      (0.254710680001 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
      exceptionalTailBill N q +
      (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1 +
      (8 * N * Real.sqrt q / q.totient) *
        (∫ y in lowHeight..middleHeight N q,
          y ^ (-3 / 2 : ℝ) * countIntegral q (0.001 * N) y (59 / 60) 1) +
      (5 * N * Real.sqrt q / q.totient) *
        ∫ y in middleHeight N q..sourceT N,
          y ^ (-2 : ℝ) * countIntegral q N y (59 / 60) 1 := by
  have hS := S_principal_and_error_paid hN hi hq hq1 heta
  have h4 := sigma4_three_source_pieces_paid hN hq.le hq1 hlow
  have h5 := equation_5_31_actual_count hN hq1
  have h6 := sigma6_low_and_endpoint_paid hN hq.le hq1 hhigh
  ring_nf at hS h4 h5 h6 ⊢
  linarith only [hS, h4, h5, h6]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
