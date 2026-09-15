import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.Count
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Assembly

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem theorem_two_closed_count {q : ℕ} [NeZero q] {x alpha : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (ha : 1 - 0.2067 / Real.log x < alpha) :
    familyCount q alpha (x / q) ≤ 2 := by
  have h := MultiZeroRepulsion.Continuation.general_theorem_two hx hq
  have hab : 1 - (2067 / 10000 : ℝ) / Real.log x < alpha := by
    simpa only [show (2067 / 10000 : ℝ) = 0.2067 by norm_num] using ha
  exact (SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.strict_to_closed_count
    hab).trans h

theorem theorem_two_input (q : ℕ) [NeZero q] :
    ∀ x : ℝ, 8000000000 ≤ x → (q : ℝ) ≤ x →
      ∀ alpha : ℝ, 1 - 0.2067 / Real.log x < alpha → alpha < 1 →
        (familyCount q alpha (x / q) : ℝ) ≤ 2 := by
  intro x hx hq alpha ha _
  exact_mod_cast theorem_two_closed_count hx hq ha

theorem actual_last_strip_inner_T2 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
    (∫ alpha in stripUpper q y..siegelCutoff q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      2 * ∫ alpha in stripUpper q y..siegelCutoff q y,
        alphaKernel (0.001 * (N : ℝ)) alpha :=
  actual_last_strip_inner hN hq hy (theorem_two_input q)

theorem actual_last_strip_log_bound_T2 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) *
      (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        ∫ alpha in stripUpper q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        ∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
          Real.exp (-z / 2) *
            (Real.exp (-((1 : ℝ) / 9.645908801) * (sourceL N + Real.log 0.001) / z) -
              Real.exp (-0.2067 * (sourceL N + Real.log 0.001) / z)) :=
  actual_last_strip_log_bound hN hq (theorem_two_input q)

theorem actual_two_strips_log_bound_T2 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) *
      (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        ∫ alpha in stripLower q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      (112000 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        (∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
          Real.exp (-z / 2) *
            (Real.exp (-0.2067 * (sourceL N + Real.log 0.001) / z) -
              Real.exp (-0.478 * (sourceL N + Real.log 0.001) / z))) +
      (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        (∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
          Real.exp (-z / 2) *
            (Real.exp (-((1 : ℝ) / 9.645908801) * (sourceL N + Real.log 0.001) / z) -
              Real.exp (-0.2067 * (sourceL N + Real.log 0.001) / z))) :=
  actual_two_strips_log_bound hN hq (theorem_two_input q)

#print axioms theorem_two_closed_count
#print axioms theorem_two_input
#print axioms actual_last_strip_inner_T2
#print axioms actual_last_strip_log_bound_T2
#print axioms actual_two_strips_log_bound_T2

end LiuWang.Proof.Campaign20260915.SecondTerminal
