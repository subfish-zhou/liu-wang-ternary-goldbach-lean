import LiuWang.Proof.Campaign20260915.ZetaValidation.Logarithm64
import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalEvaluation

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def power16Center (n : ℕ) : QComplex :=
  (reciprocalSqrtLower n 10000 * (power16Phase n).1,
   reciprocalSqrtLower n 10000 * (power16Phase n).2)

noncomputable section

open Complex

theorem power16_amplitude_parameters {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    0 ≤ reciprocalSqrtLower n 10000 ∧
      reciprocalSqrtLower n 10000 ≤ 1 ∧
      reciprocalSqrtUpper n 10000 - reciprocalSqrtLower n 10000 ≤ 1 / 10000 := by
  interval_cases n <;> norm_num [reciprocalSqrtLower, reciprocalSqrtUpper]

theorem power16_amplitude_error {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    |1 / Real.sqrt (n : ℝ) - (reciprocalSqrtLower n 10000 : ℝ)| ≤ 1 / 10000 := by
  have h := reciprocalSqrt_enclosure hn (show 1 ≤ 10000 by norm_num)
  have hb := (power16_amplitude_parameters hn hN).2.2
  have hbR : ((reciprocalSqrtUpper n 10000 - reciprocalSqrtLower n 10000 : ℚ) : ℝ) ≤
      ((1 / 10000 : ℚ) : ℝ) := Rat.cast_le.mpr hb
  push_cast at hbR
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith [h.2]

theorem cpow_critical_sixteen {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-criticalPoint 16) =
      ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        exp (((-16 * Real.log (n : ℝ) : ℝ) : ℂ) * I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : -criticalPoint 16 = -(1 / 2 : ℂ) + -16 * I := by
    apply Complex.ext <;> norm_num [criticalPoint]
  rw [hp, cpow_add _ _ hnC, cpow_neg_half_of_nat hn, cpow_def_of_ne_zero hnC]
  have hlog : log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    simpa only [ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  congr 1
  congr 1
  push_cast
  ring

theorem power16Center_correct (n : ℕ) :
    (power16Center n).toComplex =
      (reciprocalSqrtLower n 10000 : ℂ) * (power16Phase n).toComplex := by
  simp [power16Center, QComplex.toComplex]
  ring

theorem power16Center_error {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    ‖(n : ℂ) ^ (-criticalPoint 16) - (power16Center n).toComplex‖ ≤ 1 / 1000 := by
  let u := exp (((-16 * Real.log (n : ℝ) : ℝ) : ℂ) * I)
  let a : ℝ := 1 / Real.sqrt (n : ℝ)
  let c : ℝ := reciprocalSqrtLower n 10000
  have ha : |a - c| ≤ 1 / 10000 := power16_amplitude_error hn hN
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he : ‖u - (power16Phase n).toComplex‖ ≤ 1 / 5000 := power16Phase_error hn hN
  have hp := power16_amplitude_parameters hn hN
  have hc0 : 0 ≤ c := by dsimp [c]; exact_mod_cast hp.1
  have hc1 : c ≤ 1 := by dsimp [c]; exact_mod_cast hp.2.1
  rw [cpow_critical_sixteen hn, power16Center_correct]
  change ‖(a : ℂ) * u - (c : ℂ) * (power16Phase n).toComplex‖ ≤ _
  have hid : (a : ℂ) * u - (c : ℂ) * (power16Phase n).toComplex =
      ((a - c : ℝ) : ℂ) * u + (c : ℂ) * (u - (power16Phase n).toComplex) := by
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖((a - c : ℝ) : ℂ) * u‖ + ‖(c : ℂ) * (u - (power16Phase n).toComplex)‖ :=
      norm_add_le _ _
    _ = |a - c| + c * ‖u - (power16Phase n).toComplex‖ := by
      rw [norm_mul, norm_mul, hu, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0, mul_one]
    _ ≤ 1 / 10000 + 1 * (1 / 5000) :=
      add_le_add ha (mul_le_mul hc1 he (norm_nonneg _) (by norm_num))
    _ ≤ _ := by norm_num

#print axioms power16Center_error

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
