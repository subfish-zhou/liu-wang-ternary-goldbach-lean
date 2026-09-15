import LiuWang.Proof.Campaign20260915.Totient.RSZeroRegion
import LiuWang.Proof.Campaign20260915.Totient.RationalLog

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rsR_interval : (17.516 : ℝ) ≤ rsR ∧ rsR ≤ 17.517 := by
  let a := Real.sqrt (322 : ℝ)
  let b := Real.sqrt (546 : ℝ)
  have ha : a ^ 2 = 322 := Real.sq_sqrt (by norm_num)
  have hb : b ^ 2 = 546 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hab : (a * b) ^ 2 = 175812 := by rw [mul_pow, ha, hb]; norm_num
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hlo : (419.2994 : ℝ) ≤ a * b := by nlinarith
  have hhi : a * b ≤ (419.3 : ℝ) := by nlinarith
  have hd : 0 < (b - a) ^ 2 := by nlinarith
  change (17.516 : ℝ) ≤ 515 / (b - a) ^ 2 ∧ 515 / (b - a) ^ 2 ≤ 17.517
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith

theorem rs_original_scale_bounds :
    1748 ≤ rsR * (999 / 100) ^ 2 ∧ rsR * (999 / 100) ≤ 175 := by
  obtain ⟨hl, hu⟩ := rsR_interval
  constructor <;> nlinarith

theorem rs_log_two_pi_interval :
    (1.837 : ℝ) ≤ Real.log (2 * Real.pi) ∧ Real.log (2 * Real.pi) ≤ 1.838 := by
  have hlo := (rational_log_bounds (x := 6283 / 1000) (by norm_num)).1
  have hhi := (rational_log_bounds (x := 3927 / 625) (by norm_num)).2
  have hsl : logScale (6283 / 1000) = 2 := by decide +kernel
  have hsu : logScale (3927 / 625) = 2 := by decide +kernel
  have hln : (1837 / 1000 : ℚ) ≤ logLo (6283 / 1000) := by
    norm_num [logLo, logCenter, hsl, logSeries, Finset.sum_range_succ]
  have hun : logHi (3927 / 625) ≤ (919 / 500 : ℚ) := by
    norm_num [logHi, logLo, logCenter, hsu, logSeries, Finset.sum_range_succ]
  have hlnR := Rat.cast_le (K := ℝ) |>.mpr hln
  have hunR := Rat.cast_le (K := ℝ) |>.mpr hun
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlnR hunR
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  have hpL : Real.log (6283 / 1000) ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_d4])
  have hpU : Real.log (2 * Real.pi) ≤ Real.log (3927 / 625) :=
    Real.log_le_log (by positivity) (by linarith [Real.pi_lt_d4])
  constructor <;> linarith

theorem rs_original_integral_constants :
    0 < (999 / 100 : ℝ) - Real.log (2 * Real.pi) ∧
    1 / ((999 / 100 : ℝ) - Real.log (2 * Real.pi)) ≤ 0.123 ∧
    0.1592 * ((999 / 100 : ℝ) - Real.log (2 * Real.pi)) ≤ 1.298 := by
  obtain ⟨hl, hu⟩ := rs_log_two_pi_interval
  have hd : 0 < (999 / 100 : ℝ) - Real.log (2 * Real.pi) := by linarith
  refine ⟨hd, (div_le_iff₀ hd).mpr (by linarith), by linarith⟩

#print axioms rs_original_scale_bounds
#print axioms rs_original_integral_constants

end LiuWang.Proof.Campaign20260915.Totient
