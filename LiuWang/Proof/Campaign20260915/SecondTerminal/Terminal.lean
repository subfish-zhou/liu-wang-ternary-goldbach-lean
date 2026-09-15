import LiuWang.Proof.Campaign20260915.SecondTerminal.EndpointFirstPayment
import LiuWang.Proof.Campaign20260915.SecondTerminal.EndpointTotient
import LiuWang.Proof.Campaign20260915.SecondTerminal.LastBudget
import LiuWang.Proof.Campaign20260915.SecondLow.Payment

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

theorem endpoint_first_original_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    endpointFirstBill N q ≤ 0.02198 * (N : ℝ) / sourceL N :=
  endpoint_first_original_payment_of_totient hN (endpoint_totient_bound (NeZero.pos q))

theorem truncated_endpoint_original_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (16 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        (∫ alpha in (59 / 60 : ℝ)..siegelCutoff q (middleUpper N q),
          alphaKernel (0.001 * (N : ℝ)) alpha *
            (familyCount q alpha (middleUpper N q) : ℝ))) ≤
      0.022445 * (N : ℝ) / sourceL N :=
  truncated_endpoint_original_payment_of_totient hN hq hseven hnu
    (endpoint_totient_bound (NeZero.pos q))

theorem original_c1_packet_paid {N q a : ℕ} [NeZero q]
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
      (0.00104 + 0.032281 + 8 * 0.0000076 + 0.000021 + 0.000024 + 0.022445) *
        (N : ℝ) / sourceL N := by
  have h := original_c1_packet_endpoint_paid_of_totient hN hq ha eta hseven hnu
    (endpoint_totient_bound (NeZero.pos q)) hlocal
  have hl := SecondLow.originalLowScalar_bound (sourceL_ge_3100 hN)
  have hL : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have hlow := mul_le_mul_of_nonneg_right hl
    (show 0 ≤ (N : ℝ) / sourceL N by positivity)
  have hlast := mul_le_mul_of_nonneg_right originalLastScalar_fixed
    (show 0 ≤ (N : ℝ) / sourceL N by positivity)
  simp only [div_eq_mul_inv] at h hlow hlast ⊢
  nlinarith only [h, hlow, hlast]

#print axioms endpoint_first_original_payment
#print axioms truncated_endpoint_original_payment
#print axioms original_c1_packet_paid

end LiuWang.Proof.Campaign20260915.SecondTerminal
