import LiuWang.Proof.Campaign20260915.SecondTerminal.Endpoint16541

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def endpointFirstBill (N q : ℕ) : ℝ :=
  (16 * (N : ℝ) * Real.sqrt q / q.totient) *
    ((1 / Real.sqrt (middleUpper N q)) *
      ((254231 / upperLog (sourceL N) + 17102) *
        ((q : ℝ) ^ (3 : ℕ) * middleUpper N q ^ (4 : ℕ)) ^ (1 / 60 : ℝ) *
          upperLog (sourceL N) ^ (6 : ℕ) *
            Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N))))

theorem endpoint_density_first_remaining {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    endpointDensityBill N q ≤ endpointFirstBill N q + 0.00046 * (N : ℝ) / sourceL N := by
  have h := endpoint_16541_original_payment hN hnu
  unfold endpointDensityBill endpointDensityBound
  rw [(source_log_endpoints (N := N) (q := q)).2]
  unfold endpointFirstBill upperLog at h ⊢
  nlinarith only [h]

theorem truncated_endpoint_first_remaining {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (16 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        (∫ alpha in (59 / 60 : ℝ)..siegelCutoff q (middleUpper N q),
          alphaKernel (0.001 * (N : ℝ)) alpha *
            (familyCount q alpha (middleUpper N q) : ℝ))) ≤
      endpointFirstBill N q + (0.00046 + 0.0000045) * (N : ℝ) / sourceL N := by
  have h := truncated_endpoint_density_remaining hN hq hseven
  have hp := endpoint_density_first_remaining hN hnu
  simp only [div_eq_mul_inv] at h hp ⊢
  linarith

#print axioms endpoint_density_first_remaining
#print axioms truncated_endpoint_first_remaining

end LiuWang.Proof.Campaign20260915.SecondTerminal
