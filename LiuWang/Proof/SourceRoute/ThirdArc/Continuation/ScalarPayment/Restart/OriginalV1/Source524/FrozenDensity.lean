import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Coefficients
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Scale
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.LowDensity

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

def frozenDensity (q : ℕ) : ℝ :=
  16541 * heightLog (Real.log q) ^ 6 +
    (254231 / densityLog (Real.log q) + 17102) *
      ((q : ℝ) ^ 3 * (10000 * Real.log q) ^ 4) ^ (1 / 60 : ℝ) *
        densityLog (Real.log q) ^ 6

theorem densityLog_modulus {q : ℕ} (hq : 0 < q) (hs : 0 < Real.log (q : ℝ)) :
    Real.log ((q : ℝ) * (10000 * Real.log q)) = densityLog (Real.log q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.log_mul hqR.ne' (by positivity)]
  rfl

theorem original_density_frozen {q : ℕ} (hq : 0 < q) (hs : 24 ≤ Real.log (q : ℝ))
    {alpha : ℝ} (ha : 59 / 60 ≤ alpha) (ha1 : alpha ≤ 1) :
    sourceDensity q (10000 * Real.log q) alpha ≤ frozenDensity q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hy : 1 ≤ 10000 * Real.log (q : ℝ) := by linarith
  have hz := (heightLog_bounds hs).2
  have hq3 : 1 ≤ (q : ℝ) ^ (3 : ℕ) := one_le_pow₀ hqR
  have hy4 : 1 ≤ (10000 * Real.log (q : ℝ)) ^ (4 : ℕ) := one_le_pow₀ hy
  have hb : 1 ≤ (q : ℝ) ^ 3 * (10000 * Real.log q) ^ 4 := one_le_mul_of_one_le_of_one_le hq3 hy4
  have hp := Real.rpow_le_rpow_of_exponent_le hb (show 1 - alpha ≤ (1 / 60 : ℝ) by linarith)
  have hl := Real.rpow_le_rpow_of_exponent_le hz (show 6 * alpha ≤ (6 : ℕ) by norm_num; linarith)
  rw [Real.rpow_natCast] at hl
  unfold sourceDensity frozenDensity
  rw [densityLog_modulus hq (by linarith)]
  apply add_le_add le_rfl
  have h := mul_le_mul hp hl (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _)
  have hc : 0 ≤ 17102 + 254231 / densityLog (Real.log q) := by positivity
  have h := mul_le_mul_of_nonneg_left h hc
  nlinarith only [h]

theorem frozenDensity_nonneg {q : ℕ} (hs : 24 ≤ Real.log (q : ℝ)) :
    0 ≤ frozenDensity q := by
  have hz := (heightLog_bounds hs).2
  unfold frozenDensity
  positivity

theorem original_frozen_integral {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      betaKernel N alpha * sourceDensity q (10000 * Real.log q) alpha) ≤
        frozenDensity q * Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * lowHeight)) := by
  have hx := natCast_pos_of_exp_le hN
  have hL := sourceL_ge_3100 hN
  have hs := (M3_density_logs hN hq hq1).1
  have hqR : (0 : ℝ) < q := (pow_pos (by linarith : 0 < sourceL N) 3).trans_le hq
  have hqn : 0 < q := Nat.cast_pos.mp hqR
  have hab : (59 / 60 : ℝ) ≤ 1 - 0.478 / Real.log ((q : ℝ) * lowHeight) :=
    M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl
  have ht : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have hcont := (betaKernel_continuous hx).mul
    (sourceDensity_continuous hqn (by linarith [hs] : 0 < 10000 * Real.log (q : ℝ))
      (by linarith [(M3_density_logs hN hq hq1).2.1]))
  calc
    _ ≤ ∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
        frozenDensity q * betaKernel N alpha := by
      apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
        (((betaKernel_continuous hx).const_mul _).intervalIntegrable _ _)
      intro alpha ha
      have ha1 : alpha ≤ 1 := by
        have hc : 0 ≤ 0.478 / Real.log ((q : ℝ) * lowHeight) := by positivity
        linarith [ha.2]
      have hk : 0 ≤ betaKernel N alpha := by
        unfold betaKernel
        exact mul_nonneg (Real.rpow_nonneg hx.le _) (by change 0 ≤ sourceL N; linarith)
      simpa only [Pi.mul_apply, mul_comm] using
        mul_le_mul_of_nonneg_left (original_density_frozen hqn hs ha.1 ha1) hk
    _ = frozenDensity q * ((N : ℝ) ^ ((1 - 0.478 / Real.log ((q : ℝ) * lowHeight)) - 1) -
        (N : ℝ) ^ ((59 / 60 : ℝ) - 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_betaKernel hx]
    _ ≤ _ := by
      rw [cutoff_power_exp hx]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (Real.rpow_nonneg hx.le _)) (frozenDensity_nonneg hs)

theorem original_modulus_power {q : ℕ} (hq : 0 < q) (hs : 0 < Real.log (q : ℝ)) :
    Real.exp (-(1 / 2 : ℝ) * Real.log q) *
      ((q : ℝ) ^ 3 * (10000 * Real.log q) ^ 4) ^ (1 / 60 : ℝ) =
      (10 : ℝ) ^ (4 / 15 : ℝ) * Real.exp (-(9 / 20 : ℝ) * Real.log q) *
        (Real.log q) ^ (1 / 15 : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.rpow_def_of_pos (by positivity : 0 < (q : ℝ) ^ 3 * (10000 * Real.log q) ^ 4),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10), Real.rpow_def_of_pos hs,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0) hs.ne']
  rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, Real.log_pow,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num
  ring

theorem sqrt_totient_original {q : ℕ} (hq : 0 < q)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    Real.sqrt q / q.totient ≤ logNu (Real.log q) * Real.exp (-(1 / 2 : ℝ) * Real.log q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : Real.sqrt q = (q : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.log q) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hqR,
      show (q : ℝ) = Real.exp (Real.log q) from (Real.exp_log hqR).symm]
    rw [Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  rw [heq, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right htotient (Real.exp_pos _).le

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
