import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Payment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

theorem source_511_actual_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) =
      lowHeightIntegral N q +
        ∫ y in densityGate q..middleUpper N q, heightKernel y *
          ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
            alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ) := by
  have hi := (source_other_strips_integrable hN hq).1
  have hd := densityGate_le_middle hN hq
  have hlo := hi.mono_set (by
    rw [Set.uIcc_of_le hgate, Set.uIcc_of_le (middle_height_domain hN hq).2.1]
    exact Set.Icc_subset_Icc le_rfl hd)
  have hhi := hi.mono_set (by
    rw [Set.uIcc_of_le hd, Set.uIcc_of_le (middle_height_domain hN hq).2.1]
    exact Set.Icc_subset_Icc hgate le_rfl)
  exact (intervalIntegral.integral_add_adjacent_intervals hlo hhi).symm

theorem source_57_packet_low_height_paid {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((0.001 * (N : ℝ)) ^ (-(1 / 2) : ℝ) *
            bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
          (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
            alphaKernel (0.001 * (N : ℝ)) alpha *
              bandMass q alpha (omegaCutoff N q) (middleUpper N q)) +
          (1 / Real.sqrt (middleUpper N q)) *
            (∫ alpha in (59 / 60 : ℝ)..1,
              alphaKernel (0.001 * (N : ℝ)) alpha *
                (familyCount q alpha (middleUpper N q) : ℝ))) +
      (5 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((∫ y in densityGate q..(middleUpper N q), heightKernel y *
            ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) +
          (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
            ∫ alpha in stripUpper q y..1,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))) +
      0.00004366226 * (N : ℝ) / sourceL N := by
  have hp := source_57_packet_with_516_paid hN hq ha eta
  rw [source_511_actual_split hN hq hgate] at hp
  have hpay := low_height_strong_payment hN hq hgate
  simp only [div_eq_mul_inv] at hp hpay ⊢
  nlinarith only [hp, hpay]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
