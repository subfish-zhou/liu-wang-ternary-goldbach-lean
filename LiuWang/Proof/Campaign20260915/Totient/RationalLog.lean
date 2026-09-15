import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.ElementaryBounds
import Mathlib.Data.Nat.Log
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.Nu

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.Totient

def logSeries (z : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range 10, z ^ (2 * j + 1) / (2 * j + 1)

def logScale (x : ℚ) : ℕ := Nat.log 2 ⌊x⌋₊

def logCenter (x : ℚ) : ℚ :=
  let s := logScale x
  let a := x / 2 ^ s
  s * (6931471803 / 10000000000) + logSeries ((a - 1) / (a + 1))

def logLo (x : ℚ) : ℚ := (⌊logCenter x * 10000000000⌋ : ℚ) / 10000000000

def logHi (x : ℚ) : ℚ :=
  logLo x + (5 * logScale x + 11) / 10000000000

noncomputable section

private theorem logScale_bounds {x : ℚ} (hx : 1 ≤ x) :
    (2 : ℚ) ^ logScale x ≤ x ∧ x < (2 : ℚ) ^ (logScale x + 1) := by
  have hf : 0 < ⌊x⌋₊ := by
    have := (Nat.one_le_floor_iff x).mpr hx
    omega
  have hlo := Nat.pow_log_le_self 2 hf.ne'
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) ⌊x⌋₊
  constructor
  · have h : (2 : ℚ) ^ logScale x ≤ ⌊x⌋₊ := by exact_mod_cast hlo
    exact h.trans (Nat.floor_le (by linarith))
  · have h : (⌊x⌋₊ + 1 : ℚ) ≤ 2 ^ (logScale x + 1) := by
      exact_mod_cast hhi
    exact (Nat.lt_floor_add_one x).trans_le h

theorem rational_log_bounds {x : ℚ} (hx : 1 ≤ x) :
    (logLo x : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ (logHi x : ℝ) := by
  let s := logScale x
  let a : ℝ := (x : ℝ) / 2 ^ s
  let z : ℝ := (a - 1) / (a + 1)
  have hp : 0 < (2 : ℝ) ^ s := by positivity
  have hscale := logScale_bounds hx
  have ha : 1 ≤ a ∧ a < 2 := by
    constructor
    · apply (le_div_iff₀ hp).mpr
      have h : (((2 : ℚ) ^ logScale x : ℚ) : ℝ) ≤ (x : ℝ) :=
        Rat.cast_le.mpr hscale.1
      push_cast at h
      simpa only [one_mul] using h
    · apply (div_lt_iff₀ hp).mpr
      have h : (x : ℝ) < (((2 : ℚ) ^ (logScale x + 1) : ℚ) : ℝ) :=
        Rat.cast_lt.mpr hscale.2
      push_cast at h
      simpa only [pow_succ, mul_comm] using h
  have hz : 0 ≤ z ∧ z ≤ 1 / 3 := by
    dsimp [z]
    constructor
    · exact div_nonneg (by linarith) (by linarith)
    · apply (div_le_iff₀ (by linarith : 0 < a + 1)).mpr
      linarith
  have heq : (1 + z) / (1 - z) = a := by
    apply (div_eq_iff (by linarith : 1 - z ≠ 0)).mpr
    dsimp [z]
    field_simp [show a + 1 ≠ 0 by linarith]
    ring
  have hlo := Real.sum_range_le_log_div hz.1 (by linarith : z < 1) 10
  have hhi := Real.log_div_le_sum_range_add hz.1 (by linarith : z < 1) 10
  rw [heq] at hlo hhi
  have hrem : 2 * (z ^ (2 * 10 + 1) / (1 - z ^ 2)) ≤ (1 / 1000000000 : ℝ) := by
    have hs := pow_le_pow_left₀ hz.1 hz.2 2
    have ht := pow_le_pow_left₀ hz.1 hz.2 21
    have hd : (8 / 9 : ℝ) ≤ 1 - z ^ 2 := by norm_num at hs; linarith
    have h := div_le_div₀ (by positivity : (0 : ℝ) ≤ (1 / 3) ^ 21) ht
      (by norm_num : (0 : ℝ) < 8 / 9) hd
    norm_num at h
    norm_num
    linarith
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℚ) < x by linarith)
  have hid : Real.log (x : ℝ) = s * Real.log 2 + Real.log a := by
    dsimp [a]
    rw [Real.log_div hx0.ne' hp.ne', Real.log_pow]
    ring
  have hcenter : (logCenter x : ℝ) =
      s * (6931471803 / 10000000000 : ℝ) +
        2 * ∑ j ∈ Finset.range 10, z ^ (2 * j + 1) / (2 * j + 1) := by
    simp only [logCenter, logSeries, s, a, z]
    push_cast
    rfl
  have hc : (logCenter x : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ logCenter x + (5 * s + 10 : ℝ) / 10000000000 := by
    rw [hid, hcenter]
    have hl := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg s)
    have hu := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg s)
    constructor <;> nlinarith
  have hflo : (logLo x : ℚ) ≤ logCenter x := by
    unfold logLo
    exact (div_le_iff₀ (by norm_num)).mpr (Int.floor_le _)
  have hfhi : logCenter x ≤ logLo x + 1 / 10000000000 := by
    have h := Int.lt_floor_add_one (logCenter x * 10000000000)
    unfold logLo
    linarith
  constructor
  · exact (Rat.cast_le.mpr hflo).trans hc.1
  · have h : (logCenter x : ℝ) ≤ ((logLo x + 1 / 10000000000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hfhi
    push_cast at h
    unfold logHi
    push_cast
    dsimp [s] at *
    linarith [hc.2]

theorem nu_lower_from_log_bounds {x : ℝ} {a b : ℚ}
    (ha : 0 < a) (hlo : (a : ℝ) ≤ Real.log (Real.log x))
    (hhi : Real.log (Real.log x) ≤ (b : ℝ)) :
    ((178107239 / 100000000 : ℚ) * a + (250637 / 100000 : ℚ) / b : ℝ) ≤
      LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.nu x := by
  have haR : (0 : ℝ) < a := Rat.cast_pos.mpr ha
  have hlog : 0 < Real.log (Real.log x) := haR.trans_le hlo
  have hgamma :=
    LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.gammaFactor_interval.1
  change (1.78107239 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant at hgamma
  unfold LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.nu
  push_cast
  have hm := mul_le_mul hgamma hlo haR.le (Real.exp_pos _).le
  have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2.50637 by norm_num) hlog hhi
  norm_num at hm hd ⊢
  exact add_le_add hm hd

end
end LiuWang.Proof.Campaign20260915.Totient
