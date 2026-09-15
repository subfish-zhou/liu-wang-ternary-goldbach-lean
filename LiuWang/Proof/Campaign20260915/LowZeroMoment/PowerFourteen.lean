import LiuWang.Proof.Campaign20260915.ZetaValidation.Power16Evaluation

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.LowZeroMoment

open LiuWang.Proof.Campaign20260915.ZetaValidation

def power14Phase (n : ℕ) : QComplex :=
  unitRepeatedSquare 7 (-7 * logNaturalCenter n / 64)

def power14Center (n : ℕ) : QComplex :=
  (reciprocalSqrtLower n 10000 * (power14Phase n).1,
   reciprocalSqrtLower n 10000 * (power14Phase n).2)

def zeta14BlockIm (b : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 8, (power14Center (b * 8 + j + 1)).2

def zeta14TailIm : ℚ :=
  -1041 / 1570 * (power14Center 64).2 - 3584 / 785 * (power14Center 64).1

macro "certify_zeta14_block" : tactic =>
  `(tactic| (
    norm_num [zeta14BlockIm, zeta14TailIm, power14Center, reciprocalSqrtLower,
      power14Phase, logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ]
    norm_num [unitRepeatedSquare, roundQComplex, squareQComplex, unitTaylor,
      realIPower, imagIPower, roundRational, Finset.sum_range_succ]))

noncomputable section
open Complex

theorem power14Phase_error {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    ‖exp (((-14 * Real.log (n : ℝ) : ℝ) : ℂ) * I) -
      (power14Phase n).toComplex‖ ≤ 1 / 5000 := by
  have hq : |(-7 * logNaturalCenter n / 64 : ℚ)| ≤ 1 := by
    rw [abs_div, abs_mul]
    norm_num
    linarith [logNaturalCenter_bound hn hN]
  have he := unitRepeatedSquare_seven_error hq
  have hl := unitPhase_distance_le (-14 * Real.log (n : ℝ)) (-14 * (logNaturalCenter n : ℝ))
  have ha : |(-14 * Real.log (n : ℝ)) - (-14 * (logNaturalCenter n : ℝ))| ≤
      14 / 1000000 := by
    rw [show (-14 * Real.log (n : ℝ)) - (-14 * (logNaturalCenter n : ℝ)) =
      -14 * (Real.log (n : ℝ) - logNaturalCenter n) by ring, abs_mul]
    norm_num
    linarith [logNaturalCenter_error hn hN]
  have hid : (128 : ℝ) * ((-7 * logNaturalCenter n / 64 : ℚ) : ℝ) =
      -14 * (logNaturalCenter n : ℝ) := by push_cast; ring
  rw [hid] at he
  change ‖exp (((-14 * (logNaturalCenter n : ℝ) : ℝ) : ℂ) * I) -
    (power14Phase n).toComplex‖ ≤ _ at he
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (exp (((-14 * Real.log (n : ℝ) : ℝ) : ℂ) * I))
    (exp (((-14 * (logNaturalCenter n : ℝ) : ℝ) : ℂ) * I))
    (power14Phase n).toComplex
  linarith

theorem cpow_critical_fourteen {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-criticalPoint 14) =
      ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        exp (((-14 * Real.log (n : ℝ) : ℝ) : ℂ) * I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : -criticalPoint 14 = -(1 / 2 : ℂ) + -14 * I := by
    apply Complex.ext <;> norm_num [criticalPoint]
  rw [hp, cpow_add _ _ hnC, cpow_neg_half_of_nat hn, cpow_def_of_ne_zero hnC]
  have hlog : log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    simpa only [ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  congr 1
  congr 1
  push_cast
  ring

theorem power14Center_correct (n : ℕ) :
    (power14Center n).toComplex =
      (reciprocalSqrtLower n 10000 : ℂ) * (power14Phase n).toComplex := by
  simp [power14Center, QComplex.toComplex]
  ring

theorem power14Center_error {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    ‖(n : ℂ) ^ (-criticalPoint 14) - (power14Center n).toComplex‖ ≤ 3 / 10000 := by
  let u := exp (((-14 * Real.log (n : ℝ) : ℝ) : ℂ) * I)
  let a : ℝ := 1 / Real.sqrt (n : ℝ)
  let c : ℝ := reciprocalSqrtLower n 10000
  have ha : |a - c| ≤ 1 / 10000 := power16_amplitude_error hn hN
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he : ‖u - (power14Phase n).toComplex‖ ≤ 1 / 5000 := power14Phase_error hn hN
  have hp := power16_amplitude_parameters hn hN
  have hc0 : 0 ≤ c := by dsimp [c]; exact_mod_cast hp.1
  have hc1 : c ≤ 1 := by dsimp [c]; exact_mod_cast hp.2.1
  rw [cpow_critical_fourteen hn, power14Center_correct]
  change ‖(a : ℂ) * u - (c : ℂ) * (power14Phase n).toComplex‖ ≤ _
  have hid : (a : ℂ) * u - (c : ℂ) * (power14Phase n).toComplex =
      ((a - c : ℝ) : ℂ) * u + (c : ℂ) * (u - (power14Phase n).toComplex) := by
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖((a - c : ℝ) : ℂ) * u‖ + ‖(c : ℂ) * (u - (power14Phase n).toComplex)‖ :=
      norm_add_le _ _
    _ = |a - c| + c * ‖u - (power14Phase n).toComplex‖ := by
      rw [norm_mul, norm_mul, hu, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0, mul_one]
    _ ≤ 1 / 10000 + 1 * (1 / 5000) :=
      add_le_add ha (mul_le_mul hc1 he (norm_nonneg _) (by norm_num))
    _ = _ := by norm_num

#print axioms power14Center_error

end
end LiuWang.Proof.Campaign20260915.LowZeroMoment
