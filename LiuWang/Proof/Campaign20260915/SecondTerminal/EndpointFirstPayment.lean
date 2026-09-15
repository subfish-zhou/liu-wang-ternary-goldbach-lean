import LiuWang.Proof.Campaign20260915.SecondTerminal.EndpointFirstScalar
import LiuWang.Proof.Campaign20260915.SecondTerminal.CreditLedger

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

theorem endpoint_first_rpow_normalization {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (q : ℝ) * ((q : ℝ) ^ (3 : ℕ) * middleUpper N q ^ (4 : ℕ)) ^ (1 / 60 : ℝ) *
        Real.exp (-upperLog (sourceL N) / 2) =
      (q : ℝ) ^ (59 / 60 : ℝ) *
        Real.exp (-(13 / 30 : ℝ) * upperLog (sourceL N)) := by
  have hLp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hU : 0 < middleUpper N q := by unfold middleUpper; positivity
  have hlog : Real.log (middleUpper N q) =
      upperLog (sourceL N) - Real.log (q : ℝ) := by
    unfold middleUpper upperLog
    exact Real.log_div (by positivity) hq0.ne'
  rw [Real.rpow_def_of_pos (mul_pos (pow_pos hq0 3) (pow_pos hU 4)),
    Real.log_mul (pow_ne_zero 3 hq0.ne') (pow_ne_zero 4 hU.ne'),
    Real.log_pow, Real.log_pow, hlog, Real.rpow_def_of_pos hq0]
  nth_rw 1 [← Real.exp_log hq0]
  simp only [← Real.exp_add]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem endpointFirstBill_normalization {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    endpointFirstBill N q =
      16 * (N : ℝ) * ((q : ℝ) ^ (59 / 60 : ℝ) / q.totient) *
        (254231 / upperLog (sourceL N) + 17102) * upperLog (sourceL N) ^ (6 : ℕ) *
          Real.exp (-(13 / 30 : ℝ) * upperLog (sourceL N) -
            0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) := by
  have hs := endpoint_sqrt_normalization (q := q) hN
  have hr := endpoint_first_rpow_normalization (q := q) hN
  have hex : Real.exp (-(13 / 30 : ℝ) * upperLog (sourceL N) -
      0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) =
    Real.exp (-(13 / 30 : ℝ) * upperLog (sourceL N)) *
      Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold endpointFirstBill
  rw [hex]
  linear_combination
    (16 * (N : ℝ) * (254231 / upperLog (sourceL N) + 17102) *
      ((q : ℝ) ^ (3 : ℕ) * middleUpper N q ^ (4 : ℕ)) ^ (1 / 60 : ℝ) *
      upperLog (sourceL N) ^ (6 : ℕ) *
      Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N))) * hs +
    (16 * (N : ℝ) / q.totient * (254231 / upperLog (sourceL N) + 17102) *
      upperLog (sourceL N) ^ (6 : ℕ) *
      Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N))) * hr

theorem endpoint_first_original_payment_of_totient {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hphi : (q : ℝ) ^ (59 / 60 : ℝ) / q.totient ≤ 4.4772) :
    endpointFirstBill N q ≤ 0.02198 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hz : 0 < upperLog (sourceL N) :=
    (original_endpoints hL).1.trans_le (original_endpoints hL).2
  rw [endpointFirstBill_normalization hN]
  have hp := mul_le_mul_of_nonneg_right hphi
    (show 0 ≤ 16 * (N : ℝ) * (254231 / upperLog (sourceL N) + 17102) *
      upperLog (sourceL N) ^ (6 : ℕ) *
      Real.exp (-(13 / 30 : ℝ) * upperLog (sourceL N) -
        0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) by positivity)
  have hb := mul_le_mul_of_nonneg_left (endpointFirstScalar_payment (sourceL N) hL)
    (show 0 ≤ (N : ℝ) / sourceL N by positivity)
  have hn : 4.4772 *
      (16 * (N : ℝ) * (254231 / upperLog (sourceL N) + 17102) *
        upperLog (sourceL N) ^ (6 : ℕ) *
        Real.exp (-(13 / 30 : ℝ) * upperLog (sourceL N) -
          0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N))) =
      ((N : ℝ) / sourceL N) * endpointFirstScalar (sourceL N) := by
    unfold endpointFirstScalar
    field_simp
  rw [hn] at hp
  have hh := hp.trans hb
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

theorem truncated_endpoint_original_payment_of_totient {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hphi : (q : ℝ) ^ (59 / 60 : ℝ) / q.totient ≤ 4.4772) :
    (16 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        (∫ alpha in (59 / 60 : ℝ)..siegelCutoff q (middleUpper N q),
          alphaKernel (0.001 * (N : ℝ)) alpha *
            (familyCount q alpha (middleUpper N q) : ℝ))) ≤
      0.022445 * (N : ℝ) / sourceL N := by
  have he := truncated_endpoint_first_remaining hN hq hseven hnu
  have hp := endpoint_first_original_payment_of_totient hN hphi
  have hpos : 0 ≤ (N : ℝ) / sourceL N := by
    have hLp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
    positivity
  simp only [div_eq_mul_inv] at he hp hpos ⊢
  nlinarith only [he, hp, hpos]

theorem original_c1_packet_endpoint_paid_of_totient {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hphi : (q : ℝ) ^ (59 / 60 : ℝ) / q.totient ≤ 4.4772)
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (0.00104 + 0.032281 + 8 * LowHeight.originalLowScalar (sourceL N) +
        0.000021 + originalLastScalar 3100 + 0.022445) * (N : ℝ) / sourceL N := by
  have h := original_c1_packet_remaining hN hq ha eta hseven hnu hlocal
  have hp := endpoint_first_original_payment_of_totient hN hphi
  have hpos : 0 ≤ (N : ℝ) / sourceL N := by
    have hLp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
    positivity
  simp only [div_eq_mul_inv] at h hp hpos ⊢
  nlinarith only [h, hp, hpos]

#print axioms endpointFirstBill_normalization
#print axioms endpoint_first_original_payment_of_totient
#print axioms truncated_endpoint_original_payment_of_totient
#print axioms original_c1_packet_endpoint_paid_of_totient

end LiuWang.Proof.Campaign20260915.SecondTerminal
