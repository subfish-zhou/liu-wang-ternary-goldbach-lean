import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Endpoint
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.FirstMonotone
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Reduction

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

def secondPart (s : ℝ) : ℝ :=
  3100 * (1.0159 * 16541) * logNu s * heightLog s ^ 6 *
    Real.exp (-(1 / 2 : ℝ) * s - 0.478 * 3100 / (s + Real.log lowHeight))

theorem original_two_parts {s : ℝ} (hs : 24 ≤ s) :
    logBracket 3100 s = firstPart s + secondPart s := by
  have hz := (heightLog_bounds hs).2
  have hz0 : densityLog s ≠ 0 := by linarith
  unfold logBracket firstPart secondPart
  rw [Real.exp_sub, Real.exp_sub,
    show -0.478 * 3100 / (s + Real.log lowHeight) =
      -(0.478 * 3100 / (s + Real.log lowHeight)) by ring, Real.exp_neg]
  field_simp

theorem firstPart_endpoint : firstPart (6 * Real.log 3100) ≤ (0.249809 : ℝ) := by
  have hs := log_3100_precise
  have hs24 : 24 ≤ 6 * Real.log (3100 : ℝ) := by linarith [hs.1]
  have hn0 := (logNu_bounds hs24).2
  have hz0 := (heightLog_bounds hs24).2
  have hp := add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ densityLog (6 * Real.log 3100))
      endpoint_logs.2 5) (by norm_num : (0 : ℝ) ≤ 254231))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ densityLog (6 * Real.log 3100))
      endpoint_logs.2 6) (by norm_num : (0 : ℝ) ≤ 17102))
  have h := mul_le_mul (mul_le_mul (mul_le_mul endpoint_nu endpoint_power
    (Real.rpow_nonneg (by linarith) _) (by norm_num)) hp (by positivity) (by norm_num))
    (Real.exp_le_exp.mpr endpoint_exponent) (Real.exp_pos _).le (by norm_num)
  have h := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3100 * 1.8771)
  apply le_trans (b := (3100 * 1.8771 * (1.781074 * 3.8760838 + 2.50637 / 3.8760837) *
    1.294864 * (254231 * (61.3213686 : ℝ) ^ 5 + 17102 * (61.3213686 : ℝ) ^ 6)) *
      Real.exp (-46.9967238))
  · unfold firstPart
    nlinarith only [h]
  · exact endpoint_rational_certificate

theorem secondPart_exponent {s : ℝ} (hs : 24 ≤ s) :
    -(1 / 2 : ℝ) * s - 0.478 * 3100 / (s + Real.log lowHeight) ≤ -49.25 := by
  have ht : 0 < s + Real.log lowHeight := by linarith [lowHeight_log_bounds.1]
  have hq : (54.43 - (s + Real.log lowHeight) / 2) * (s + Real.log lowHeight) ≤
      (0.478 : ℝ) * 3100 := by
    nlinarith [sq_nonneg (s + Real.log lowHeight - 54.43)]
  have hd := (le_div_iff₀ ht).mpr hq
  linarith [original_height_precise]

theorem secondPart_rational_certificate :
    (3100 * (1.0159 * 16541) * 7.56 * (13.087 : ℝ) ^ 6) *
      Real.exp (-49.25) ≤ (1 / 1000000 : ℝ) := by
  have h := exp_nat_add_lower 49 6 (u := 0.25) (by norm_num) (le_refl _)
  norm_num only [Nat.cast_ofNat, show (49 : ℝ) + 0.25 = 49.25 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
  linarith only [h]

theorem secondPart_paid {s : ℝ} (hs : 24 ≤ s) (hs1 : s ≤ 6 * Real.log 3100) :
    secondPart s ≤ (1 / 1000000 : ℝ) := by
  have hs0 : 0 < s := by linarith
  have ht24 : 24 ≤ 6 * Real.log (3100 : ℝ) := hs.trans hs1
  have hnu : logNu s ≤ (7.56 : ℝ) :=
    (logNu_monotone hs ht24 hs1).trans (endpoint_nu.trans (by norm_num))
  have hn0 := (logNu_bounds hs).2
  have hh0 := (heightLog_bounds hs).1
  have hh : heightLog s ≤ (13.087 : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < 10000 * s)
      (mul_le_mul_of_nonneg_left hs1 (by norm_num : (0 : ℝ) ≤ 10000))
    exact h.trans (endpoint_logs.1.trans (by norm_num))
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ heightLog s) hh 6
  have h := mul_le_mul (mul_le_mul hnu hp (by positivity) (by norm_num))
    (Real.exp_le_exp.mpr (secondPart_exponent hs)) (Real.exp_pos _).le (by norm_num)
  have h := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3100 * (1.0159 * 16541))
  apply le_trans (b := (3100 * (1.0159 * 16541) * 7.56 * (13.087 : ℝ) ^ 6) *
    Real.exp (-49.25))
  · unfold secondPart
    nlinarith only [h]
  · exact secondPart_rational_certificate

theorem logBracket_base_paid {s : ℝ} (hs : 24 ≤ s) (hs1 : s ≤ 6 * Real.log 3100) :
    logBracket 3100 s ≤ (24981 / 100000 : ℝ) := by
  have ht24 : 24 ≤ 6 * Real.log (3100 : ℝ) := hs.trans hs1
  have ht48 : 6 * Real.log (3100 : ℝ) ≤ 48.24 := by linarith [log_3100_precise.2]
  have h1 := (firstPart_monotone ⟨hs, hs1.trans ht48⟩ ⟨ht24, ht48⟩ hs1).trans firstPart_endpoint
  have h2 := secondPart_paid hs hs1
  rw [original_two_parts hs]
  linarith only [h1, h2]

theorem originalBracket_paid (L x : ℝ) (hL : 3100 ≤ L) (hx : 3 ≤ x) (hx1 : x ≤ 6) :
    originalBracket L x ≤ (24981 / 100000 : ℝ) := by
  apply (originalBracket_reduce_L hL hx hx1).trans
  have hl : 0 < Real.log (3100 : ℝ) := Real.log_pos (by norm_num)
  rw [originalBracket_eq_logBracket (by norm_num : (0 : ℝ) < 3100) (by linarith) hl]
  apply logBracket_base_paid
  · have h := mul_le_mul_of_nonneg_right hx hl.le
    linarith [log_3100_precise.1]
  · exact mul_le_mul_of_nonneg_right hx1 hl.le

theorem modulus_bracket_paid {L : ℝ} {q : ℕ} (hL : 3100 ≤ L)
    (hq : L ^ (3 : ℕ) ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ L ^ (6 : ℕ)) :
    logBracket L (Real.log q) ≤ (24981 / 100000 : ℝ) := by
  have hx := modulus_parameter hL hq hq1
  rw [← modulus_logBracket hL hq hq1]
  exact originalBracket_paid L _ hL hx.1 hx.2.1

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
