import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.LowAlpha
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.Endpoint

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

theorem endpoint_alpha_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in (59 / 60 : ℝ)..1,
      alphaKernel (0.001 * (N : ℝ)) alpha *
        (familyCount q alpha (middleUpper N q) : ℝ)) =
      (∫ alpha in (59 / 60 : ℝ)..stripLower q (middleUpper N q),
        alphaKernel (0.001 * (N : ℝ)) alpha *
          (familyCount q alpha (middleUpper N q) : ℝ)) +
      (∫ alpha in stripLower q (middleUpper N q)..1,
        alphaKernel (0.001 * (N : ℝ)) alpha *
          (familyCount q alpha (middleUpper N q) : ℝ)) := by
  have hx : 0 < 0.001 * (N : ℝ) := by
    have hn := natCast_pos_of_exp_le hN
    positivity
  have hi (a b : ℝ) : IntervalIntegrable
      (fun alpha => alphaKernel (0.001 * (N : ℝ)) alpha *
        (familyCount q alpha (middleUpper N q) : ℝ)) volume a b := by
    by_cases hab : a ≤ b
    · exact count_alpha_integrable hx hab _
    · exact (count_alpha_integrable hx (le_of_not_ge hab) _).symm
  exact (intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)).symm

theorem middlePacket_low_alpha_and_endpoint_tail_paid {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((1 / Real.sqrt (middleUpper N q)) *
          ∫ alpha in (59 / 60 : ℝ)..stripLower q (middleUpper N q),
            alphaKernel (0.001 * (N : ℝ)) alpha *
              (familyCount q alpha (middleUpper N q) : ℝ)) +
      (5 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((∫ y in densityGate q..middleUpper N q, heightKernel y *
            ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) +
          (∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
            ∫ alpha in stripUpper q y..1,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))) +
      0.00069366226 * (N : ℝ) / sourceL N +
      (0.0004 * (N : ℝ) / sourceL N) *
        (1 - Real.exp (-0.478 * (sourceL N + Real.log 0.001) /
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))) := by
  have hp := source_57_packet_low_height_paid hN hq hgate ha eta
  rw [endpoint_alpha_split hN] at hp
  have hlow := actual_low_alpha_strong_payment hN hq
  have htail := endpoint_tail_difference_payment hN hq
  simp only [div_eq_mul_inv] at hp hlow htail ⊢
  nlinarith only [hp, hlow, htail]

theorem middlePacket_low_alpha_and_endpoint_tail_paid_all_heights {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((1 / Real.sqrt (middleUpper N q)) *
          ∫ alpha in (59 / 60 : ℝ)..stripLower q (middleUpper N q),
            alphaKernel (0.001 * (N : ℝ)) alpha *
              (familyCount q alpha (middleUpper N q) : ℝ)) +
      (5 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
            ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) +
          (∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
            ∫ alpha in stripUpper q y..1,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))) +
      0.0006611104 * (N : ℝ) / sourceL N +
      (0.0004 * (N : ℝ) / sourceL N) *
        (1 - Real.exp (-0.478 * (sourceL N + Real.log 0.001) /
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))) := by
  have hp := source_57_packet_with_516_paid hN hq ha eta
  rw [endpoint_alpha_split hN] at hp
  have hlow := actual_low_alpha_strong_payment hN hq
  have htail := endpoint_tail_difference_payment hN hq
  simp only [div_eq_mul_inv] at hp hlow htail ⊢
  nlinarith only [hp, hlow, htail]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
