import LiuWang.Proof.Campaign20260915.SecondTerminal.Terminal
import LiuWang.Proof.WeightedHighZeros.Packet

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.DirichletZeroCount hiding heightKernel zeroValues mem_zeroValues
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def originalLowPacket (N q a : ℕ) [NeZero q] (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ (zeroValues chi (sourceT N)).filter (fun rho => |rho.im| < omegaCutoff N q),
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def originalHighPacket (N q a : ℕ) [NeZero q] (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ (zeroValues chi (sourceT N)).filter (fun rho => middleUpper N q < |rho.im|),
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem highPacket_eq_original_middle_add_high {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (a : ℕ) (eta : ℝ) :
    WeightedHighZeros.highPacket N q a eta =
      middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta +
        originalHighPacket N q a eta := by
  have hh := middle_height_domain hN hq
  have hmid (chi : Character q) :
      (WeightedHighZeros.highValues N chi).filter (fun rho => |rho.im| ≤ middleUpper N q) =
        (zeroValues chi (middleUpper N q)).filter (fun rho => omegaCutoff N q ≤ |rho.im|) := by
    ext rho
    simp only [WeightedHighZeros.highValues_eq_complete, Finset.mem_filter, mem_zeroValues]
    constructor
    · rintro ⟨⟨⟨hz, h0, h1, _, hb⟩, hw⟩, hu⟩
      exact ⟨⟨hz, h0, h1, hu, hb⟩, hw⟩
    · rintro ⟨⟨hz, h0, h1, hu, hb⟩, hw⟩
      exact ⟨⟨⟨hz, h0, h1, hu.trans hh.2.2, hb⟩, hw⟩, hu⟩
  have hhigh (chi : Character q) :
      (WeightedHighZeros.highValues N chi).filter (fun rho => ¬ |rho.im| ≤ middleUpper N q) =
        (zeroValues chi (sourceT N)).filter (fun rho => middleUpper N q < |rho.im|) := by
    ext rho
    simp only [WeightedHighZeros.highValues_eq_complete, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hr, _⟩, hu⟩
      exact ⟨hr, hu⟩
    · rintro ⟨hr, hu⟩
      exact ⟨⟨hr, hh.2.1.trans hu.le⟩, hu⟩
  have hs (chi : Character q) :
      (∑ rho ∈ WeightedHighZeros.highValues N chi,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta) =
      (∑ rho ∈ (zeroValues chi (middleUpper N q)).filter (fun rho => omegaCutoff N q ≤ |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta) +
      ∑ rho ∈ (zeroValues chi (sourceT N)).filter (fun rho => middleUpper N q < |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
    rw [← hmid chi, ← hhigh chi]
    exact (Finset.sum_filter_add_sum_filter_not (WeightedHighZeros.highValues N chi)
      (fun rho => |rho.im| ≤ middleUpper N q)
      (fun rho => (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta)).symm
  rw [middlePacket_eq_complete]
  simp only [WeightedHighZeros.highPacket, originalHighPacket, hs, mul_add, Finset.sum_add_distrib]

theorem zeroPacket_eq_original_three_packets {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ) :
    zeroPacket q N a eta =
      originalLowPacket N q a eta +
        middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta +
          originalHighPacket N q a eta := by
  have h := WeightedHighZeros.complete_zeroPacket_split ha eta (N := N)
  change zeroPacket q N a eta =
    originalLowPacket N q a eta + WeightedHighZeros.highPacket N q a eta at h
  rw [highPacket_eq_original_middle_add_high hN hq] at h
  simpa only [add_assoc] using h

theorem S_le_original_outer_packets {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      ‖principalCoefficient q * J N eta‖ + errorBound q N a eta +
      ‖originalLowPacket N q a eta‖ +
      (0.00104 + 0.032281 + 8 * 0.0000076 + 0.000021 + 0.000024 + 0.022445) *
        (N : ℝ) / sourceL N + ‖originalHighPacket N q a eta‖ := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have he := complete_error_function hN0 hi (hq.trans (sourceP_le_sourceP1 hN0)) eta
  have hm := original_c1_packet_paid hN hq hi.2.2 eta hseven hnu hlocal
  have hp : ‖zeroPacket q N a eta‖ ≤
      ‖originalLowPacket N q a eta‖ +
        ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ +
          ‖originalHighPacket N q a eta‖ := by
    rw [zeroPacket_eq_original_three_packets hN hq hi.2.2]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hid : S N (rationalCenter a q + eta) =
      (S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
        zeroPacket q N a eta) + principalCoefficient q * J N eta -
        zeroPacket q N a eta := by ring
  have hs : ‖S N (rationalCenter a q + eta)‖ ≤
      ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
        zeroPacket q N a eta‖ + ‖principalCoefficient q * J N eta‖ +
        ‖zeroPacket q N a eta‖ := by
    conv_lhs => rw [hid]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  linarith only [he, hm, hp, hs]

#print axioms zeroPacket_eq_original_three_packets
#print axioms S_le_original_outer_packets

end LiuWang.Proof.Campaign20260915.SecondTerminal
