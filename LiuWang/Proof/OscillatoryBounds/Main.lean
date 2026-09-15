import LiuWang.Proof.Interfaces.Main
import LiuWang.Proof.VaughanTypeI.Geometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# 原窗振荡积分的基础界

以下实端点定理不改变 `Interfaces.J`、`Interfaces.Jrho`。
倒数界显式要求频率非零；可积性由原窗上的连续性给出。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.VaughanTypeI (norm_charReal_eq_one)

namespace LiuWang.Proof.OscillatoryBounds

theorem continuous_charReal_mul (η : ℝ) :
    Continuous (fun t : ℝ => charReal (η * t)) := by
  unfold charReal
  fun_prop

theorem intervalIntegrable_charReal (a b η : ℝ) :
    IntervalIntegrable (fun t => charReal (η * t)) volume a b :=
  (continuous_charReal_mul η).intervalIntegrable a b

theorem norm_integral_charReal_le_length {a b : ℝ} (hab : a ≤ b) (η : ℝ) :
    ‖∫ t in a..b, charReal (η * t)‖ ≤ b - a := by
  simpa only [one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1) (fun t _ => (norm_charReal_eq_one (η * t)).le))

theorem charReal_mul_eq_exp (η t : ℝ) :
    charReal (η * t) = Complex.exp ((2 * Real.pi * η * Complex.I) * t) := by
  unfold charReal
  push_cast
  congr 1
  ring

theorem norm_frequency (η : ℝ) :
    ‖(2 * Real.pi * η * Complex.I : ℂ)‖ = 2 * Real.pi * |η| := by
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem integral_charReal_eq {a b η : ℝ} (hη : η ≠ 0) :
    (∫ t in a..b, charReal (η * t)) =
      (charReal (η * b) - charReal (η * a)) / (2 * Real.pi * η * Complex.I) := by
  simp_rw [charReal_mul_eq_exp]
  apply integral_exp_mul_complex
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Complex.ofReal_ne_zero.mpr hη))
    Complex.I_ne_zero

theorem norm_integral_charReal_le_reciprocal (a b : ℝ) {η : ℝ} (hη : η ≠ 0) :
    ‖∫ t in a..b, charReal (η * t)‖ ≤ 1 / (Real.pi * |η|) := by
  rw [integral_charReal_eq hη, norm_div, norm_frequency]
  calc
    ‖charReal (η * b) - charReal (η * a)‖ / (2 * Real.pi * |η|) ≤
        2 / (2 * Real.pi * |η|) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [norm_charReal_eq_one, one_add_one_eq_two] using
        norm_sub_le (charReal (η * b)) (charReal (η * a))
    _ = 1 / (Real.pi * |η|) := by ring

theorem continuousOn_cpow_charReal {a b : ℝ} (ha : 0 < a) (rho : ℂ) (η : ℝ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (rho - 1) * charReal (η * t))
      (Set.Icc a b) := by
  intro t ht
  exact ((Complex.continuousAt_ofReal_cpow_const t (rho - 1)
    (Or.inr (ne_of_gt (ha.trans_le ht.1)))).mul
      (continuous_charReal_mul η).continuousAt).continuousWithinAt

theorem intervalIntegrable_cpow_charReal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (rho : ℂ) (η : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (rho - 1) * charReal (η * t))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact continuousOn_cpow_charReal ha rho η

theorem norm_cpow_charReal {t : ℝ} (ht : 0 < t) (rho : ℂ) (η : ℝ) :
    ‖(t : ℂ) ^ (rho - 1) * charReal (η * t)‖ = t ^ (rho.re - 1) := by
  rw [norm_mul, norm_charReal_eq_one, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

theorem norm_integral_cpow_charReal_le_weight {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {rho : ℂ} (hbeta : 0 < rho.re) (η : ℝ) :
    ‖∫ t in a..b, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      (b ^ rho.re - a ^ rho.re) / rho.re := by
  calc
    _ ≤ ∫ t in a..b, ‖(t : ℂ) ^ (rho - 1) * charReal (η * t)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, t ^ (rho.re - 1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact norm_cpow_charReal (ha.trans_le ht.1) rho η
    _ = (b ^ rho.re - a ^ rho.re) / rho.re := by
      rw [integral_rpow (Or.inl (by linarith : -1 < rho.re - 1))]
      simp

theorem norm_integral_cpow_charReal_le_source_weight {N : ℝ} (hN : 0 < N)
    {rho : ℂ} (hbeta : 0 < rho.re) (η : ℝ) :
    ‖∫ t in N / 1000..N, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      (1 - (0.001 : ℝ) ^ rho.re) / rho.re * N ^ rho.re := by
  have h := norm_integral_cpow_charReal_le_weight (by positivity : 0 < N / 1000)
    (by linarith : N / 1000 ≤ N) hbeta η
  have hp : (N / 1000) ^ rho.re = (0.001 : ℝ) ^ rho.re * N ^ rho.re := by
    rw [show N / 1000 = (0.001 : ℝ) * N by ring,
      Real.mul_rpow (by norm_num) hN.le]
  rw [hp] at h
  convert h using 1
  ring

end LiuWang.Proof.OscillatoryBounds
