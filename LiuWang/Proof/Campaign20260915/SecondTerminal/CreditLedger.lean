import LiuWang.Proof.Campaign20260915.SecondTerminal.PacketDensityRemaining
import LiuWang.Proof.Campaign20260915.ThirdDomainTail.SecondPacket

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem original_truncated_height_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    heightMass N q (fun _ => 59 / 60) (siegelCutoff q) =
      LowHeight.actualM1 N q + actualStripIntegral N q +
        heightMass N q (stripUpper q) (siegelCutoff q) := by
  have hcut (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
      1 / 2 ≤ siegelCutoff q y := by
    have h := sparse_cutoff_order (middle_log_domain hN hq hy).2.1
    exact h.1.trans h.2.1
  have hs := heightMass_add hN hq (fun _ => 59 / 60) (siegelCutoff q) (fun _ => 1)
    continuousOn_const (siegelCutoff_continuous hN hq) continuousOn_const
    (by intros; norm_num) hcut (by intros; norm_num)
  linarith only [hs, original_height_split hN hq]

theorem original_c1_packet_coefficients {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (16 * (N : ℝ) * Real.sqrt q / q.totient) *
        (lowAlphaMass N q +
          (1 / Real.sqrt (middleUpper N q)) *
            alphaMass N q (middleUpper N q) (59 / 60)
              (siegelCutoff q (middleUpper N q))) +
        (8 * (N : ℝ) * Real.sqrt q / q.totient) *
          heightMass N q (fun _ => 59 / 60) (siegelCutoff q) := by
  have hp := ThirdDomainTail.middlePacket_original_c1_count_reduction hN hq ha eta hlocal
  change ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
    (10 * (N : ℝ) * Real.sqrt q / q.totient) *
      (lowAlphaMass N q +
        (1 / Real.sqrt (middleUpper N q)) *
          alphaMass N q (middleUpper N q) (59 / 60)
            (siegelCutoff q (middleUpper N q)) +
        (1 / 2 : ℝ) * heightMass N q (fun _ => 59 / 60) (siegelCutoff q)) at hp
  have hn := norm_nonneg (middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta)
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith only [hp, hn]

theorem original_c1_packet_remaining {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (0.00104 + 0.032281 + 8 * LowHeight.originalLowScalar (sourceL N) +
        0.000021 + originalLastScalar 3100 + 0.00046 + 0.0000045) *
          (N : ℝ) / sourceL N + endpointFirstBill N q := by
  have hp := original_c1_packet_coefficients hN hq ha eta hlocal
  rw [original_truncated_height_split hN hq] at hp
  have hlo := mul_le_mul_of_nonneg_left (actual_low_alpha_normalized hN hq)
    (show 0 ≤ (16 : ℝ) * N by positivity)
  simp only [neg_div] at hlo
  change 16 * (N : ℝ) * ((Real.sqrt q / q.totient) * lowAlphaMass N q) ≤ _ at hlo
  have hm1 := mul_le_mul_of_nonneg_left
    (LowHeight.actual_M1_le_original_low_scalar hN hq hseven hnu) (Nat.cast_nonneg N)
  have h516 := actual_516_payment_of_source_totient hN hq hnu
  have h517 := actual_last_strip_le_fixed_scalar hN hq hnu
  change (8 * (N : ℝ) * Real.sqrt q / q.totient) *
    heightMass N q (stripUpper q) (siegelCutoff q) ≤
      ((N : ℝ) / sourceL N) * originalLastScalar 3100 at h517
  have hep := truncated_endpoint_first_remaining hN hq hseven hnu
  change (16 * (N : ℝ) * Real.sqrt q / q.totient) *
    ((1 / Real.sqrt (middleUpper N q)) *
      alphaMass N q (middleUpper N q) (59 / 60) (siegelCutoff q (middleUpper N q))) ≤
        endpointFirstBill N q + (0.00046 + 0.0000045) * (N : ℝ) / sourceL N at hep
  simp only [div_eq_mul_inv] at hp hlo hm1 h516 h517 hep ⊢
  nlinarith only [hp, hlo, hm1, h516, h517, hep]

#print axioms original_truncated_height_split
#print axioms original_c1_packet_coefficients
#print axioms original_c1_packet_remaining

end LiuWang.Proof.Campaign20260915.SecondTerminal
