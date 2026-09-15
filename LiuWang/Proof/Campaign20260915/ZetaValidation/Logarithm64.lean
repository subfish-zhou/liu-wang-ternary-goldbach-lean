import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalUnitPhase
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def logNaturalRaw (n : ℕ) : ℚ :=
  (n.log2 + 1) * (287209 / 414355) -
    ∑ j ∈ Finset.range 24, (1 - n / (2 : ℚ) ^ (n.log2 + 1)) ^ (j + 1) / (j + 1)

def logNaturalCenter (n : ℕ) : ℚ := roundRational (logNaturalRaw n)

def power16Phase (n : ℕ) : QComplex :=
  unitRepeatedSquare 7 (-logNaturalCenter n / 8)

noncomputable section

open Complex Finset

theorem logNatural_parameters {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    n.log2 + 1 ≤ 7 ∧
      0 ≤ (1 - (n : ℚ) / 2 ^ (n.log2 + 1)) ∧
      (1 - (n : ℚ) / 2 ^ (n.log2 + 1)) ≤ 1 / 2 := by
  interval_cases n <;> norm_num [Nat.log2_eq_log_two]

theorem logNaturalRaw_error {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    |Real.log (n : ℝ) - (logNaturalRaw n : ℝ)| ≤ 1 / 10000000 := by
  have hp := logNatural_parameters hn hN
  have hk : ((n.log2 + 1 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast hp.1
  have hx0 : 0 ≤ (1 - (n : ℝ) / 2 ^ (n.log2 + 1)) := by
    have h : ((0 : ℚ) : ℝ) ≤ ((1 - (n : ℚ) / 2 ^ (n.log2 + 1) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hp.2.1
    simpa using h
  have hx1 : (1 - (n : ℝ) / 2 ^ (n.log2 + 1)) ≤ 1 / 2 := by
    have h : ((1 - (n : ℚ) / 2 ^ (n.log2 + 1) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hp.2.2
    simpa using h
  have hx : |1 - (n : ℝ) / 2 ^ (n.log2 + 1)| ≤ 1 / 2 := by
    rwa [abs_of_nonneg hx0]
  have ht := Real.abs_log_sub_add_sum_range_le (lt_of_le_of_lt hx (by norm_num)) 24
  have hb : |1 - (n : ℝ) / 2 ^ (n.log2 + 1)| ^ (24 + 1) /
      (1 - |1 - (n : ℝ) / 2 ^ (n.log2 + 1)|) ≤ (1 / 2 : ℝ) ^ 25 * 2 := by
    rw [div_eq_mul_inv]
    gcongr
    · exact inv_nonneg.mpr (by linarith)
    · rw [← one_div, div_le_iff₀ (by linarith)]
      linarith
  have hl : |((n.log2 + 1 : ℕ) : ℝ) * (Real.log 2 - 287209 / 414355)| ≤
      ((n.log2 + 1 : ℕ) : ℝ) / 10000000000 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.log2 + 1))]
    have h := mul_le_mul_of_nonneg_left Real.log_two_near_10
      (Nat.cast_nonneg (n.log2 + 1) : (0 : ℝ) ≤ (n.log2 + 1 : ℕ))
    norm_num at h
    push_cast
    linarith only [h]
  have hid : Real.log (n : ℝ) =
      ((n.log2 + 1 : ℕ) : ℝ) * Real.log 2 +
        Real.log ((n : ℝ) / 2 ^ (n.log2 + 1)) := by
    rw [Real.log_div (by exact_mod_cast (show n ≠ 0 by omega)) (by positivity),
      Real.log_pow]
    ring
  have ht' := ht.trans hb
  rw [show (1 : ℝ) - (1 - (n : ℝ) / 2 ^ (n.log2 + 1)) =
    (n : ℝ) / 2 ^ (n.log2 + 1) by ring] at ht'
  rw [hid, logNaturalRaw]
  push_cast
  rw [abs_le] at hl ht' ⊢
  norm_num at ht'
  push_cast at hl hk
  constructor <;> linarith [hl.1, hl.2, ht'.1, ht'.2]

theorem logNaturalCenter_error {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    |Real.log (n : ℝ) - (logNaturalCenter n : ℝ)| ≤ 1 / 1000000 := by
  have hl := logNaturalRaw_error hn hN
  have hr := roundRational_error (logNaturalRaw n)
  have ht := abs_sub_le (Real.log (n : ℝ)) (logNaturalRaw n : ℝ)
    (logNaturalCenter n : ℝ)
  rw [abs_sub_comm (logNaturalRaw n : ℝ)] at ht
  change |(logNaturalCenter n : ℝ) - (logNaturalRaw n : ℝ)| ≤ _ at hr
  linarith

theorem logNaturalCenter_bound {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    |logNaturalCenter n| ≤ 8 := by
  have he := abs_le.mp (logNaturalCenter_error hn hN)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNR : (n : ℝ) ≤ 64 := by exact_mod_cast hN
  have hl := Real.log_nonneg hnR
  have hu := Real.log_le_log (by linarith : (0 : ℝ) < n) hNR
  have hlog : Real.log 64 = 6 * Real.log 2 := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 6 = 64 by norm_num] using Real.log_pow 2 6
  rw [hlog] at hu
  have h2 := abs_le.mp Real.log_two_near_10
  have hr : |(logNaturalCenter n : ℝ)| ≤ 8 := by
    rw [abs_le]
    constructor <;> linarith [he.1, he.2, h2.1, h2.2]
  exact_mod_cast hr

theorem power16Phase_error {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    ‖exp (((-16 * Real.log (n : ℝ) : ℝ) : ℂ) * I) -
      (power16Phase n).toComplex‖ ≤ 1 / 5000 := by
  have hq : |(-logNaturalCenter n / 8 : ℚ)| ≤ 1 := by
    rw [abs_div, abs_neg]
    norm_num
    linarith [logNaturalCenter_bound hn hN]
  have he := unitRepeatedSquare_seven_error hq
  have hl := unitPhase_distance_le (-16 * Real.log (n : ℝ)) (-16 * (logNaturalCenter n : ℝ))
  have ha : |(-16 * Real.log (n : ℝ)) - (-16 * (logNaturalCenter n : ℝ))| ≤
      16 / 1000000 := by
    rw [show (-16 * Real.log (n : ℝ)) - (-16 * (logNaturalCenter n : ℝ)) =
      -16 * (Real.log (n : ℝ) - logNaturalCenter n) by ring, abs_mul]
    norm_num
    linarith [logNaturalCenter_error hn hN]
  have hid : (128 : ℝ) * ((-logNaturalCenter n / 8 : ℚ) : ℝ) =
      -16 * (logNaturalCenter n : ℝ) := by push_cast; ring
  rw [hid] at he
  change ‖exp (((-16 * (logNaturalCenter n : ℝ) : ℝ) : ℂ) * I) -
    (power16Phase n).toComplex‖ ≤ _ at he
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (exp (((-16 * Real.log (n : ℝ) : ℝ) : ℂ) * I))
    (exp (((-16 * (logNaturalCenter n : ℝ) : ℝ) : ℂ) * I))
    (power16Phase n).toComplex
  linarith

#print axioms logNaturalCenter_error
#print axioms power16Phase_error

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
