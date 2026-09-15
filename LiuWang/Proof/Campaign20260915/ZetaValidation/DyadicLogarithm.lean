import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalAngle
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def logOneMinusSeries (x : ℚ) (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range m, x ^ (j + 1) / (j + 1)

def dyadicLog (q : ℚ) (k m : ℕ) : ℚ :=
  k * logOneMinusSeries (1 / 2) m - logOneMinusSeries (1 - q / 2 ^ k) m

noncomputable section

theorem logOneMinusSeries_error {x : ℚ} (hx : |x| ≤ 1 / 2) (m : ℕ) :
    |Real.log (1 - (x : ℝ)) + (logOneMinusSeries x m : ℝ)| ≤ (1 / 2 : ℝ) ^ m := by
  have hxR : |(x : ℝ)| ≤ 1 / 2 := by
    have h : ((|x| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hx
    simpa using h
  have h := Real.abs_log_sub_add_sum_range_le (lt_of_le_of_lt hxR (by norm_num)) m
  have hb : |(x : ℝ)| ^ (m + 1) / (1 - |(x : ℝ)|) ≤ (1 / 2 : ℝ) ^ m := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ (m + 1) * 2 := by
        rw [div_eq_mul_inv]
        gcongr
        · exact inv_nonneg.mpr (by linarith)
        · rw [← one_div, div_le_iff₀ (by linarith)]
          linarith
      _ = _ := by rw [pow_succ]; ring
  unfold logOneMinusSeries
  push_cast
  simpa only [add_comm] using h.trans hb

theorem dyadicLog_error {q : ℚ} {k : ℕ}
    (hlo : 1 / 2 ≤ q / 2 ^ k) (hhi : q / 2 ^ k ≤ 1) (m : ℕ) :
    |Real.log (q : ℝ) - (dyadicLog q k m : ℝ)| ≤
      ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by
  have hq : (0 : ℝ) < q := by
    have h : (0 : ℚ) < q / 2 ^ k := lt_of_lt_of_le (by norm_num) hlo
    have : (0 : ℚ) < q :=
      (div_pos_iff_of_pos_right (by positivity : (0 : ℚ) < 2 ^ k)).mp h
    exact_mod_cast this
  have hx : |(1 - q / 2 ^ k : ℚ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h1 := logOneMinusSeries_error hx m
  have h2 := logOneMinusSeries_error (x := 1 / 2) (by norm_num) m
  have he : Real.log (1 - (1 / 2 : ℚ)) = -Real.log 2 := by
    norm_num
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he] at h2
  have heq : Real.log (q : ℝ) =
      (k : ℝ) * Real.log 2 + Real.log ((q : ℝ) / 2 ^ k) := by
    rw [Real.log_div hq.ne' (by positivity), Real.log_pow]
    ring
  have hid : 1 - ((1 - q / 2 ^ k : ℚ) : ℝ) = (q : ℝ) / 2 ^ k := by
    push_cast
    ring
  rw [hid] at h1
  have hsum := abs_add_le
    ((k : ℝ) * (Real.log 2 - (logOneMinusSeries (1 / 2) m : ℝ)))
    (Real.log ((q : ℝ) / 2 ^ k) + (logOneMinusSeries (1 - q / 2 ^ k) m : ℝ))
  have hl : |Real.log 2 - (logOneMinusSeries (1 / 2) m : ℝ)| ≤ (1 / 2 : ℝ) ^ m := by
    rw [abs_le] at h2 ⊢
    constructor <;> linarith [h2.1, h2.2]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)] at hsum
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hc : Real.log (q : ℝ) - (dyadicLog q k m : ℝ) =
      (k : ℝ) * (Real.log 2 - (logOneMinusSeries (1 / 2) m : ℝ)) +
        (Real.log ((q : ℝ) / 2 ^ k) + (logOneMinusSeries (1 - q / 2 ^ k) m : ℝ)) := by
    rw [heq]
    simp only [dyadicLog, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast]
    ring
  rw [hc]
  linarith

#print axioms dyadicLog_error

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
