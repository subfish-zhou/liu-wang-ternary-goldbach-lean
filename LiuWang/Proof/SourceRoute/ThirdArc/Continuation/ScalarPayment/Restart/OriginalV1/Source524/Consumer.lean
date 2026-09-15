import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.FrozenDensity
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Payment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

theorem original_frozen_weight {q : ℕ} (hq : 0 < q) (hs : 24 ≤ Real.log (q : ℝ))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    (Real.sqrt q / q.totient) * lowCoefficient (59 / 60) * frozenDensity q ≤
      1.8771 * Real.exp (-(9 / 20 : ℝ) * Real.log q) * logNu (Real.log q) *
        (Real.log q) ^ (1 / 15 : ℝ) *
          (254231 / densityLog (Real.log q) + 17102) * densityLog (Real.log q) ^ 6 +
      1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * Real.log q) * logNu (Real.log q) *
        heightLog (Real.log q) ^ 6 := by
  have hs0 : 0 < Real.log (q : ℝ) := by linarith
  have hnu := (logNu_bounds hs).2
  have hz := (heightLog_bounds hs).2
  have hC : 0 ≤ 254231 / densityLog (Real.log q) + 17102 := by positivity
  have hc := lowCoefficient_nonneg (by norm_num : (0 : ℝ) < 59 / 60)
  have hD := frozenDensity_nonneg hs
  have hw := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sqrt_totient_original hq htotient) hc) hD
  have heq : Real.exp (-(1 / 2 : ℝ) * Real.log q) * lowCoefficient (59 / 60) * frozenDensity q =
      (lowCoefficient (59 / 60) * (10 : ℝ) ^ (4 / 15 : ℝ)) *
        Real.exp (-(9 / 20 : ℝ) * Real.log q) * (Real.log q) ^ (1 / 15 : ℝ) *
        (254231 / densityLog (Real.log q) + 17102) * densityLog (Real.log q) ^ 6 +
      lowCoefficient (59 / 60) * 16541 * Real.exp (-(1 / 2 : ℝ) * Real.log q) *
        heightLog (Real.log q) ^ 6 := by
    calc
      _ = lowCoefficient (59 / 60) * (254231 / densityLog (Real.log q) + 17102) *
          densityLog (Real.log q) ^ 6 *
          (Real.exp (-(1 / 2 : ℝ) * Real.log q) *
            ((q : ℝ) ^ 3 * (10000 * Real.log q) ^ 4) ^ (1 / 60 : ℝ)) +
          lowCoefficient (59 / 60) * 16541 * Real.exp (-(1 / 2 : ℝ) * Real.log q) *
            heightLog (Real.log q) ^ 6 := by unfold frozenDensity; ring
      _ = _ := by rw [original_modulus_power hq hs0]; ring
  have hw' : (Real.sqrt q / q.totient) * lowCoefficient (59 / 60) * frozenDensity q ≤
      logNu (Real.log q) *
        (Real.exp (-(1 / 2 : ℝ) * Real.log q) * lowCoefficient (59 / 60) * frozenDensity q) := by
    nlinarith only [hw]
  rw [heq] at hw'
  have h1 := mul_le_mul_of_nonneg_right original_decimal_coefficients.2
    (show 0 ≤ Real.exp (-(9 / 20 : ℝ) * Real.log q) * (Real.log q) ^ (1 / 15 : ℝ) *
      (254231 / densityLog (Real.log q) + 17102) * densityLog (Real.log q) ^ 6 by positivity)
  have h2 := mul_le_mul_of_nonneg_right original_decimal_coefficients.1
    (show 0 ≤ 16541 * Real.exp (-(1 / 2 : ℝ) * Real.log q) * heightLog (Real.log q) ^ 6 by positivity)
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hnu
  nlinarith only [hw', h]

theorem lowDensityBill_le_originalBracket {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    lowDensityBill N q ≤ (N : ℝ) / sourceL N *
      originalBracket (sourceL N) (Real.log q / Real.log (sourceL N)) := by
  have hx := natCast_pos_of_exp_le hN
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hs := (M3_density_logs hN hq hq1).1
  have hqR : (0 : ℝ) < q := (pow_pos hL0 3).trans_le hq
  have hqn : 0 < q := Nat.cast_pos.mp hqR
  have hlog : Real.log ((q : ℝ) * lowHeight) = Real.log q + Real.log lowHeight :=
    Real.log_mul hqR.ne' (by unfold lowHeight; positivity)
  have hi := mul_le_mul_of_nonneg_left (original_frozen_integral hN hq hq1)
    (show 0 ≤ ((N : ℝ) * Real.sqrt q / q.totient) * lowCoefficient (59 / 60) from
      mul_nonneg (by positivity) (lowCoefficient_nonneg (by norm_num)))
  have hw := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (original_frozen_weight hqn hs htotient)
      (Real.exp_pos (-0.478 * sourceL N / Real.log ((q : ℝ) * lowHeight))).le) hx.le
  rw [hlog] at hi hw
  rw [modulus_logBracket hL hq hq1]
  unfold lowDensityBill
  rw [hlog]
  unfold logBracket
  have hcancel : (N : ℝ) / sourceL N * (sourceL N *
      (1.8771 * Real.exp (-(9 / 20 : ℝ) * Real.log q) * logNu (Real.log q) *
          (Real.log q) ^ (1 / 15 : ℝ) *
          (254231 / densityLog (Real.log q) + 17102) * densityLog (Real.log q) ^ 6 +
        1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * Real.log q) * logNu (Real.log q) *
          heightLog (Real.log q) ^ 6) *
      Real.exp (-0.478 * sourceL N / (Real.log q + Real.log lowHeight))) =
      (N : ℝ) *
        (1.8771 * Real.exp (-(9 / 20 : ℝ) * Real.log q) * logNu (Real.log q) *
          (Real.log q) ^ (1 / 15 : ℝ) *
          (254231 / densityLog (Real.log q) + 17102) * densityLog (Real.log q) ^ 6 +
        1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * Real.log q) * logNu (Real.log q) *
          heightLog (Real.log q) ^ 6) *
      Real.exp (-0.478 * sourceL N / (Real.log q + Real.log lowHeight)) := by
    field_simp
  rw [hcancel]
  simp only [div_eq_mul_inv] at hi hw ⊢
  nlinarith only [hi, hw]

theorem equation_5_24_original_bill {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    lowDensityBill N q ≤ (24981 / 100000 : ℝ) * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hx := modulus_parameter hL hq hq1
  have hpaid := originalBracket_paid (sourceL N) _ hL hx.1 hx.2.1
  have h := mul_le_mul_of_nonneg_left hpaid
    (show 0 ≤ (N : ℝ) / sourceL N by exact div_nonneg (Nat.cast_nonneg _) (by linarith))
  have hb := lowDensityBill_le_originalBracket hN hq hq1 htotient
  simp only [div_eq_mul_inv] at hb h ⊢
  nlinarith only [hb, h]

theorem equation_5_24_original_contribution {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
      (∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
        betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      (24981 / 100000 : ℝ) * (N : ℝ) / sourceL N :=
  (low_count_integral_le_densityBill hN hq hq1 hdensity).trans
    (equation_5_24_original_bill hN hq hq1 htotient)

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
