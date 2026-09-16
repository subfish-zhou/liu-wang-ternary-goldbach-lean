import LiuWang.Proof.Campaign20260915.ZetaValidation.Logarithm64

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundFiftyPhase (n : ℕ) : QComplex :=
  unitRepeatedSquare 7 (-25 * logNaturalCenter n / 64)

noncomputable section
open Complex Finset

theorem backlund_fifty_seed_bound {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10) :
    |(-25 * logNaturalCenter n / 64 : ℚ)| ≤ 1 := by
  have hl := abs_le.mp (logNaturalCenter_error hn (by omega : n ≤ 64))
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (n : ℝ) ≤ 10 := by exact_mod_cast hn'
  have he : (10 : ℝ) < Real.exp (12 / 5) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12 / 5) 7
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hu : Real.log (n : ℝ) ≤ 12 / 5 :=
    (Real.log_le_iff_le_exp hnp).mpr (hN.trans he.le)
  have hlo : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hq : |(logNaturalCenter n : ℝ)| ≤ 5 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hl.1, hl.2]
  have hqR : ((|logNaturalCenter n| : ℚ) : ℝ) ≤ ((5 / 2 : ℚ) : ℝ) := by
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using hq
  have hq' : |logNaturalCenter n| ≤ (5 / 2 : ℚ) := Rat.cast_le.mp hqR
  rw [abs_div, abs_mul]
  norm_num
  linarith

theorem backlundFiftyPhase_error {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10) :
    ‖Complex.exp (((-50 * Real.log (n : ℝ) : ℝ) : ℂ) * I) -
      (backlundFiftyPhase n).toComplex‖ ≤ 13747 / 100000000 := by
  have he := unitRepeatedSquare_error (backlund_fifty_seed_bound hn hn')
    (k := 7) (by norm_num)
  have hl := unitPhase_distance_le (-50 * Real.log (n : ℝ)) (-50 * (logNaturalCenter n : ℝ))
  have ha : |(-50 * Real.log (n : ℝ)) - (-50 * (logNaturalCenter n : ℝ))| ≤
      50 / 1000000 := by
    rw [show -50 * Real.log (n : ℝ) - -50 * (logNaturalCenter n : ℝ) =
      -50 * (Real.log (n : ℝ) - logNaturalCenter n) by ring, abs_mul]
    norm_num
    linarith [logNaturalCenter_error hn (by omega : n ≤ 64)]
  have hid : (2 : ℝ) ^ 7 * ((-25 * logNaturalCenter n / 64 : ℚ) : ℝ) =
      -50 * (logNaturalCenter n : ℝ) := by push_cast; ring
  rw [hid] at he
  change ‖Complex.exp (((-50 * (logNaturalCenter n : ℝ) : ℝ) : ℂ) * I) -
    (backlundFiftyPhase n).toComplex‖ ≤ _ at he
  have h := norm_sub_le_norm_sub_add_norm_sub
    (Complex.exp (((-50 * Real.log (n : ℝ) : ℝ) : ℂ) * I))
    (Complex.exp (((-50 * (logNaturalCenter n : ℝ) : ℝ) : ℂ) * I))
    (backlundFiftyPhase n).toComplex
  replace he : ‖Complex.exp (((-50 * (logNaturalCenter n : ℝ) : ℝ) : ℂ) * I) -
      (backlundFiftyPhase n).toComplex‖ ≤ 8747 / 100000000 :=
    he.trans_eq (by norm_num)
  linarith

theorem backlundFiftyPhase_two :
    backlundFiftyPhase 2 = (-9950193 / 10000000, 1993517 / 20000000) := by
  norm_num [backlundFiftyPhase, logNaturalCenter, logNaturalRaw, roundRational,
    Nat.log2_eq_log_two, Finset.sum_range_succ]
  norm_num [unitRepeatedSquare, roundQComplex, squareQComplex, unitTaylor,
    realIPower, imagIPower, roundRational, Finset.sum_range_succ]

#print axioms backlund_fifty_seed_bound
#print axioms backlundFiftyPhase_error
#print axioms backlundFiftyPhase_two

end
end LiuWang.Proof.Campaign20260915.RosserCount
