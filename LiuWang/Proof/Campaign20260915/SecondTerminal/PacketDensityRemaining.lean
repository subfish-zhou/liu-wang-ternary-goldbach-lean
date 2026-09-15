import LiuWang.Proof.Campaign20260915.SecondTerminal.OriginalLedger
import LiuWang.Proof.Campaign20260915.SecondTerminal.LastScaling
import LiuWang.Proof.Campaign20260915.SecondTerminal.EndpointDensitySplit

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

theorem original_packet_density_remaining {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (0.00104 + 0.032281 + 8 * LowHeight.originalLowScalar (sourceL N) +
        0.000021 + 0.00046 + 0.0000045) * (N : ℝ) / sourceL N +
      lastStripLogBill N q + endpointFirstBill N q +
      (16 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((1 / Real.sqrt (middleUpper N q)) *
          alphaMass N q (middleUpper N q) (siegelCutoff q (middleUpper N q)) 1) +
      (8 * (N : ℝ) * Real.sqrt q / q.totient) *
        heightMass N q (siegelCutoff q) (fun _ => 1) := by
  have h := original_packet_reduction hN hq ha eta hseven hnu
  have he := endpoint_density_first_remaining hN hnu
  simp only [div_eq_mul_inv] at h he ⊢
  nlinarith only [h, he]

#print axioms original_packet_density_remaining
#print axioms originalLastScalar_le_base
#print axioms endpoint_16541_original_payment

end LiuWang.Proof.Campaign20260915.SecondTerminal
