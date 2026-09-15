import LiuWang.Proof.Campaign20260915.SecondTerminal.HighArc
import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceFreeConsumers

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem original_c1_packet_region_paid {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (0.00104 + 0.032281 + 8 * 0.0000076 + 0.000021 + 0.000024 + 0.022445) *
        (N : ℝ) / sourceL N :=
  original_c1_packet_paid hN hq ha eta hseven hnu
    (fun _ hy => OriginalRegion.original_middle_local_source_free hN hq hy.1)

theorem original_high_packet_region_paid {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ}
    (heta : |eta| ≤ 1 / ((q : ℝ) * sourceQ N))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖originalHighPacket N q a eta‖ ≤
      (5 * 0.0126 * sourceNu (sourceP N)) * (N : ℝ) /
        (sourceL N ^ (2 : ℕ) * Real.sqrt (sourceL N)) :=
  original_high_packet_payment hN hq ha heta hRS hseven hnu
    (fun _ hy => OriginalRegion.original_middle_local_source_free hN hq hy.1)

theorem S_le_original_low_remaining_region_paid {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ)
    (hlo : deltaRadius N q < |eta|)
    (hhi : |eta| ≤ 1 / ((q : ℝ) * sourceQ N))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      (10 * (N : ℝ) / (3.36 * sourceP N)) * sourceNu (sourceP N) +
      4.3368 * (N : ℝ) / sourceL N ^ (6 : ℕ) +
      ‖originalLowPacket N q a eta‖ +
      (0.00104 + 0.032281 + 8 * 0.0000076 + 0.000021 + 0.000024 + 0.022445) *
        (N : ℝ) / sourceL N +
      (5 * 0.0126 * sourceNu (sourceP N)) * (N : ℝ) /
        (sourceL N ^ (2 : ℕ) * Real.sqrt (sourceL N)) :=
  S_le_original_low_remaining hN hq hi eta hlo hhi hRS hseven hnu
    (fun _ hy => OriginalRegion.original_middle_local_source_free hN hq hy.1)

#print axioms original_c1_packet_region_paid
#print axioms original_high_packet_region_paid
#print axioms S_le_original_low_remaining_region_paid

end LiuWang.Proof.Campaign20260915.SecondTerminal
