import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.VerifiedArithmetic

/-! # The certified (2.32) payment, with no numerical hypothesis -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem source32_uniform {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (L ^ (18 : ℕ)),
      L ^ (4 : ℕ) * Real.exp (-s) * source31Profile L s) ≤
      368 / 1000000000000000 :=
  source32_uniform_of_fixed_certificate fixed_arithmetic_certificate hL

theorem actual_source32 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * lambdaCountSegment N q y 0.36 0.478) ≤
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ) :=
  actual_source32_of_fixed_certificate fixed_arithmetic_certificate hN hq

theorem highSum_le_unpaid_add_source32 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y * unpaidAlpha N q y) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ)) :=
  highSum_le_unpaid_add_source32_of_fixed_certificate fixed_arithmetic_certificate hN hq

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
