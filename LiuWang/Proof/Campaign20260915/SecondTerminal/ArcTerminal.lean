import LiuWang.Proof.Campaign20260915.SecondTerminal.OuterScalar
import LiuWang.Proof.MinorArcEnergy.Ledger

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ArcGeometry LiuWang.Proof.MinorArcEnergy
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem S_original_4012 {N q a : ℕ} [NeZero q]
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
    ‖S N (rationalCenter a q + eta)‖ ≤ 0.4012 * (N : ℝ) / sourceL N := by
  have hL : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have hs := S_le_original_low_remaining_region_paid hN hq hi eta hlo hhi hRS hseven hnu
  have hl := original_low_packet_cases hN hq hi.2.2 hlo hnu
  have ho := original_outer_payment (sourceL_ge_3100 hN) (Nat.cast_nonneg N (α := ℝ))
  have hb := mul_le_mul_of_nonneg_right
    (by norm_num :
      (0.3452 + (0.00104 + 0.032281 + 8 * 0.0000076 + 0.000021 + 0.000024 + 0.022445) : ℝ)
        ≤ 0.4012) (show 0 ≤ (N : ℝ) / sourceL N by positivity)
  simp only [sourceP, div_eq_mul_inv] at hs hl ho hb ⊢
  linarith only [hs, hl, ho, hb]

theorem M2_original_4012 {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hseven : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ∀ alpha ∈ M2 N, ‖S N alpha‖ ≤ 0.4012 * (N : ℝ) / sourceL N := by
  intro alpha ha
  obtain ⟨q, a, eta, hq, hi, he, hlo, hhi⟩ := M2_eta_range ha
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  rw [he]
  exact S_original_4012 hN hq hi eta hlo hhi hRS (hseven q hq) (hnu q hq)

theorem M2_integral_original_4012 {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hseven : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * ∫ alpha in M2 N, ‖S N alpha‖ ^ 2 :=
  norm_setIntegral_le_local_energy N (measurableSet_M2 N)
    (M2_subset_sourceDomain (exp_2000_le_of_exp_3100_le hN))
    (M2_original_4012 hN hRS hseven hnu)

#print axioms S_original_4012
#print axioms M2_original_4012
#print axioms M2_integral_original_4012

end LiuWang.Proof.Campaign20260915.SecondTerminal
