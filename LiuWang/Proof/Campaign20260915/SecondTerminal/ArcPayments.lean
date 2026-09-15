import LiuWang.Proof.Campaign20260915.SecondTerminal.ArcAssembly
import LiuWang.Proof.NearArcPayment.Payment

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem principal_original_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {eta : ℝ}
    (heta : deltaRadius N q < |eta|)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖principalCoefficient q * J N eta‖ ≤
      (10 * (N : ℝ) / (3.36 * sourceP N)) * sourceNu (sourceP N) := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hP := sourceP_pos hN0
  have hm : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hmass : principalMass q * (q : ℝ) ≤ sourceNu (sourceP N) := by
    calc
      _ = |(ArithmeticFunction.moebius q : ℝ)| * ((q : ℝ) / q.totient) := by
        unfold principalMass
        ring
      _ ≤ (q : ℝ) / q.totient := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hm
          (show 0 ≤ (q : ℝ) / q.totient by positivity)
      _ ≤ _ := hnu
  have hp := mul_le_mul_of_nonneg_right hmass
    (show 0 ≤ (10 / 3.36 : ℝ) * (N : ℝ) / sourceP N by positivity)
  apply (NearArcPayment.principal_payment hN0 (NeZero.pos q) heta).trans
  unfold NearArcPayment.principalPayment
  simp only [div_eq_mul_inv, mul_inv_rev] at hp ⊢
  nlinarith only [hp]

theorem perron_original_payment {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) {eta : ℝ}
    (heta : |eta| ≤ 1 / ((q : ℝ) * sourceQ N)) :
    errorBound q N a eta ≤ 4.3368 * (N : ℝ) / sourceL N ^ (6 : ℕ) := by
  apply (NearArcPayment.perron_payment (exp_2000_le_of_exp_3100_le hN) hi hq heta).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (3.025 : ℝ) ≤ 4.3368) (Nat.cast_nonneg N))
    (pow_nonneg (by linarith [sourceL_ge_3100 hN]) 6)

theorem S_le_original_low_high {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ)
    (hlo : deltaRadius N q < |eta|)
    (hhi : |eta| ≤ 1 / ((q : ℝ) * sourceQ N))
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      (10 * (N : ℝ) / (3.36 * sourceP N)) * sourceNu (sourceP N) +
      4.3368 * (N : ℝ) / sourceL N ^ (6 : ℕ) +
      ‖originalLowPacket N q a eta‖ +
      (0.00104 + 0.032281 + 8 * 0.0000076 + 0.000021 + 0.000024 + 0.022445) *
        (N : ℝ) / sourceL N + ‖originalHighPacket N q a eta‖ := by
  have hs := S_le_original_outer_packets hN hq hi eta hseven hnu hlocal
  have hp := principal_original_payment hN hlo hnu
  have he := perron_original_payment hN hq hi hhi
  linarith only [hs, hp, he]

#print axioms principal_original_payment
#print axioms perron_original_payment
#print axioms S_le_original_low_high

end LiuWang.Proof.Campaign20260915.SecondTerminal
