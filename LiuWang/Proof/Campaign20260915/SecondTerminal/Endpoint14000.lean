import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.Endpoint
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Endpoint

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

theorem exp_neg_five_le : Real.exp (-5 : ℝ) ≤ 0.007 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
    (show (2.7 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 5
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos (5 : ℝ))).mpr
  linarith

theorem endpoint_exponential_le {L : ℝ} (hL : 3100 ≤ L) :
    Real.exp (-0.10367089 * (L + Real.log 0.001) /
      Real.log (10 * Real.pi * L ^ (7 : ℕ))) ≤ 0.007 := by
  have hs := scaling_bounds hL
  have hu := original_upper_le_scaling hL
  have hH := original_H_ge_scaling hL
  have he := original_endpoints hL
  have hu0 : 0 < Real.log (10 * Real.pi * L ^ (7 : ℕ)) := he.1.trans_le he.2
  have hsq := mul_nonneg (show 0 ≤ scaling L by linarith)
    (sub_nonneg.mpr hs.1)
  have hratio : 5 ≤ 0.10367089 * (L + Real.log 0.001) /
      Real.log (10 * Real.pi * L ^ (7 : ℕ)) := by
    apply (le_div_iff₀ hu0).mpr
    nlinarith only [hu, hH, hsq, hs.1]
  apply le_trans (Real.exp_le_exp.mpr ?_) exp_neg_five_le
  simpa only [neg_div, neg_mul] using neg_le_neg hratio

def endpointDensityBill (N q : ℕ) : ℝ :=
  (16 * (N : ℝ) * Real.sqrt q / q.totient) *
    ((1 / Real.sqrt (middleUpper N q)) *
      (endpointDensityBound q (middleUpper N q) *
        Real.exp (-0.478 * (sourceL N + Real.log 0.001) /
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))))

theorem endpoint_14000_original_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (16 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        (14000 * Real.exp (-0.10367089 * (sourceL N + Real.log 0.001) /
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ))))) ≤
      0.0000045 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hnorm := endpoint_normalization_bound hN hq
  have he := endpoint_exponential_le hL
  have hpaid := mul_le_mul hnorm he (Real.exp_pos _).le
    (show 0 ≤ (0.0004 : ℝ) / sourceL N by positivity)
  have hm := mul_le_mul_of_nonneg_left hpaid
    (show 0 ≤ (8 / 5 : ℝ) * N by positivity)
  have hNL : 0 ≤ (N : ℝ) / sourceL N := by positivity
  simp only [div_eq_mul_inv] at hm hNL ⊢
  nlinarith only [hm, hNL]

theorem truncated_endpoint_density_remaining {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y) :
    (16 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        (∫ alpha in (59 / 60 : ℝ)..siegelCutoff q (middleUpper N q),
          alphaKernel (0.001 * (N : ℝ)) alpha *
            (familyCount q alpha (middleUpper N q) : ℝ))) ≤
      endpointDensityBill N q + 0.0000045 * (N : ℝ) / sourceL N := by
  have hb := mul_le_mul_of_nonneg_left (truncated_endpoint_bound hN hq hseven)
    (show 0 ≤ 16 * (N : ℝ) * Real.sqrt q / q.totient by positivity)
  have hp := endpoint_14000_original_payment hN hq
  unfold endpointDensityBill
  simp only [div_eq_mul_inv] at hb hp ⊢
  nlinarith only [hb, hp]

#print axioms endpoint_14000_original_payment
#print axioms truncated_endpoint_density_remaining

end LiuWang.Proof.Campaign20260915.SecondTerminal
