import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowAssembly
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact beta integration of the explicit Theorem 7 density powers. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

def sourceDensity (q : ℕ) (y alpha : ℝ) : ℝ :=
  16541 * Real.log y ^ 6 +
    (17102 + 254231 / Real.log ((q : ℝ) * y)) *
      ((q : ℝ) ^ 3 * y ^ 4) ^ (1 - alpha) *
        Real.log ((q : ℝ) * y) ^ (6 * alpha)

theorem integral_exp_affine {k : ℝ} (hk : k ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Real.exp (k * (x - 1))) =
      (Real.exp (k * (b - 1)) - Real.exp (k * (a - 1))) / k := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := fun x => Real.exp (k * (x - 1)) / k)
    (f' := fun x => Real.exp (k * (x - 1)))
    (fun x _ => by
      simpa only [mul_one, mul_div_cancel_right₀ _ hk] using!
        (((hasDerivAt_id x).sub_const 1).const_mul k).exp.div_const k)
    (show IntervalIntegrable (fun x => Real.exp (k * (x - 1))) volume a b from
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _)
  exact h.trans (by ring)

theorem integral_density_exponential {L D a b : ℝ} (hk : 0 < L - D)
    (hL : 0 ≤ L) :
    (∫ alpha in a..b, L * Real.exp (L * (alpha - 1)) *
        Real.exp (D * (1 - alpha))) ≤
      L / (L - D) * Real.exp ((L - D) * (b - 1)) := by
  have he (alpha : ℝ) :
      L * Real.exp (L * (alpha - 1)) * Real.exp (D * (1 - alpha)) =
        L * Real.exp ((L - D) * (alpha - 1)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_exp_affine hk.ne']
  have h := mul_le_mul_of_nonneg_left
    (sub_le_self (Real.exp ((L - D) * (b - 1)))
      (Real.exp_pos ((L - D) * (a - 1))).le)
    (div_nonneg hL hk.le)
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using h

theorem density_power_envelope {q : ℕ} (hq : 0 < q) {y alpha : ℝ}
    (hy : 1 ≤ y) (hs : 1 ≤ Real.log ((q : ℝ) * y))
    (ha : alpha ≤ 1) :
    sourceDensity q y alpha ≤
      16541 * Real.log y ^ 6 +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          Real.log ((q : ℝ) * y) ^ 6 *
          Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hprod : (q : ℝ) ^ 3 * y ^ 4 ≤ ((q : ℝ) * y) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hqR (pow_nonneg hq0.le 3)
    nlinarith [mul_nonneg (show 0 ≤ (q : ℝ) ^ 4 - (q : ℝ) ^ 3 by nlinarith) (pow_nonneg hy0.le 4)]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (q : ℝ) ^ 3 * y ^ 4)
    hprod (by linarith : 0 ≤ 1 - alpha)
  have hl := Real.rpow_le_rpow_of_exponent_le hs
    (show 6 * alpha ≤ (6 : ℕ) by norm_num; linarith)
  rw [Real.rpow_natCast] at hl
  have hexp : (((q : ℝ) * y) ^ (4 : ℕ)) ^ (1 - alpha) =
      Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
    norm_num
  rw [hexp] at hp
  unfold sourceDensity
  apply add_le_add le_rfl
  have hc : 0 ≤ 17102 + 254231 / Real.log ((q : ℝ) * y) := by positivity
  have h := mul_le_mul hp hl (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left h hc
  nlinarith only [h]

theorem sourceDensity_continuous {q : ℕ} (hq : 0 < q) {y : ℝ}
    (hy : 0 < y) (hs : 0 < Real.log ((q : ℝ) * y)) :
    Continuous (sourceDensity q y) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hp : (q : ℝ) ^ 3 * y ^ 4 ≠ 0 := by positivity
  have hs0 := hs.ne'
  unfold sourceDensity
  fun_prop

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
