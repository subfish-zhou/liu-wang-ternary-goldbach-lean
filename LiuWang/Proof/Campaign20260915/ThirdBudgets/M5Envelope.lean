import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityScalar
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Constants

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem m5_exponent_amgm {L t : ℝ} (hL : 3100 ≤ L) (ht : 0 < t) :
    49.69 * Real.sqrt (L / 3100) ≤ (5 / 12 : ℝ) * t + 0.478 * L / t := by
  have hs := Real.sq_sqrt (show 0 ≤ L / 3100 by positivity)
  have hsq := sq_nonneg ((5 / 12 : ℝ) * t - (49.69 / 2) * Real.sqrt (L / 3100))
  rw [show (5 / 12 : ℝ) * t + 0.478 * L / t =
    ((5 / 12 : ℝ) * t ^ 2 + 0.478 * L) / t by field_simp]
  apply (le_div_iff₀ ht).mpr
  nlinarith only [hs, hsq, hL]

theorem m5_kernel_envelope {L t : ℝ} (hL : 3100 ≤ L) (ht : 59.4 ≤ t) :
    (33643 + 254231 / t) * t ^ 6 * Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t) ≤
      37924 * 60 ^ 6 *
        Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100)) := by
  have ht0 : 0 < t := by linarith
  have hc : (33643 : ℝ) + 254231 / t ≤ 37924 := by
    have hd : (254231 : ℝ) / t ≤ 4281 :=
      (div_le_iff₀ ht0).mpr (by linarith)
    linarith only [hd]
  have hpow := sixth_power_tangent ht0.le
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul hc hpow (pow_nonneg ht0.le 6) (by norm_num))
    (Real.exp_pos (-(14 / 15 : ℝ) * t - 0.478 * L / t)).le
  calc
    _ ≤ 37924 * (60 ^ 6 * Real.exp (t / 10 - 6)) *
        Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t) := h
    _ = 37924 * 60 ^ 6 *
        Real.exp (t / 10 - 6 + (-(14 / 15 : ℝ) * t - 0.478 * L / t)) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [m5_exponent_amgm hL ht0])) (by norm_num)

theorem integral_m5_affine_envelope (L a b : ℝ) :
    (∫ t in a..b,
      Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100))) =
      (12 / 5 : ℝ) * Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
        (Real.exp (-(5 / 12 : ℝ) * a) - Real.exp (-(5 / 12 : ℝ) * b)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := fun t => -(12 / 5 : ℝ) *
      Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100)))
    (f' := fun t => Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100)))
    (fun t _ => by
      have hd := (((((hasDerivAt_id t).const_mul (-(5 / 12 : ℝ))).sub_const 6).sub_const
        (49.69 * Real.sqrt (L / 3100))).exp.const_mul (-(12 / 5 : ℝ)))
      simp only [id_eq] at hd
      convert hd using 1
      · rfl
      · ring)
    ((by fun_prop : Continuous (fun t : ℝ =>
      Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100)))).intervalIntegrable a b)
  rw [h]
  have he (t : ℝ) :
      Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100)) =
        Real.exp (-(5 / 12 : ℝ) * t) *
          Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he a, he b]
  ring

theorem m5_finite_integral_envelope {L a b : ℝ}
    (hL : 3100 ≤ L) (ha : 59.4 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b,
      (33643 + 254231 / t) * t ^ 6 *
        Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t)) ≤
      (12 / 5 : ℝ) * 37924 * 60 ^ 6 *
        Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
        (Real.exp (-(5 / 12 : ℝ) * a) - Real.exp (-(5 / 12 : ℝ) * b)) := by
  have hi : IntervalIntegrable (fun t : ℝ =>
      (33643 + 254231 / t) * t ^ 6 *
        Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    fun_prop
  have he : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100))) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ =>
      Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100)))).intervalIntegrable a b
  calc
    _ ≤ ∫ t in a..b, 37924 * 60 ^ 6 *
        Real.exp (-(5 / 12 : ℝ) * t - 6 - 49.69 * Real.sqrt (L / 3100)) := by
      apply intervalIntegral.integral_mono_on hab hi (he.const_mul _)
      intro t ht
      exact m5_kernel_envelope hL (ha.trans ht.1)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_m5_affine_envelope]
      ring

theorem original_m5_finite_integral_envelope {L : ℝ} (hL : 3100 ≤ L) :
    (∫ t in Real.log (10 * Real.pi * L ^ 7)..Real.log (L ^ 21),
      (33643 + 254231 / t) * t ^ 6 *
        Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t)) ≤
      (12 / 5 : ℝ) * 37924 * 60 ^ 6 *
        Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
        (Real.exp (-(5 / 12 : ℝ) * Real.log (10 * Real.pi * L ^ 7)) -
          Real.exp (-(5 / 12 : ℝ) * Real.log (L ^ 21))) := by
  have hL0 : 0 < L := by linarith
  have hl : 8 ≤ Real.log L :=
    LiuWang.Proof.WeightedLowZeros.Continuation.log_3100_bounds.1.trans
      (Real.log_le_log (by norm_num) hL)
  apply m5_finite_integral_envelope hL ?_ (M6Certificate.original_log_interval hL).2
  rw [Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0)
    (pow_pos hL0 7).ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [M6Certificate.log_ten_pi_bounds.1]

#print axioms m5_kernel_envelope
#print axioms original_m5_finite_integral_envelope

end LiuWang.Proof.Campaign20260915.ThirdBudgets
