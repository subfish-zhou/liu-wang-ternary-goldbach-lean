import LiuWang.Proof.Campaign20260915.Totient.ThetaDecay
import AnalyticNumberTheory.Mertens.Theorems

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.Mertens
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

theorem theta_error_integral_le_log_cube {x : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x) :
    ‖∫ t in Ioi x, thetaErrorKernel t‖ ≤ 1030 / Real.log x ^ 3 := by
  have hL := log_large_of_tail hx
  have hx1 : 1 < x := (Real.log_pos_iff hx0.le).mp (by linarith)
  apply (norm_integral_Ioi_le_div_log (f := thetaErrorKernel)
    (C := 1030 / Real.log x ^ 2) hx1 ?_).trans_eq (by ring)
  intro t ht
  have ht0 : 0 < t := hx0.trans ht
  have hlogs := Real.log_le_log hx0 ht.le
  have htlog := hx.trans hlogs
  have htL := log_large_of_tail htlog
  have he := theta_error_le_log_cube ht0 htlog
  have hf : 0 ≤ (Real.log t + 1) / (t * Real.log t) ^ 2 := by positivity
  have hf' : (Real.log t + 1) / (t * Real.log t) ^ 2 ≤ 2 / (t ^ 2 * Real.log t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hl : Real.log t + 1 ≤ 2 * Real.log t := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg t),
      mul_le_mul_of_nonneg_left hl (mul_nonneg (sq_nonneg t) (by linarith : 0 ≤ Real.log t))]
  have hsq : Real.log x ^ 2 ≤ Real.log t ^ 2 :=
    pow_le_pow_left₀ (by linarith) hlogs 2
  have hcoeff : 1030 / Real.log t ^ 2 ≤ 1030 / Real.log x ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
  calc
    ‖thetaErrorKernel t‖ = |Chebyshev.theta t - t| *
        ((Real.log t + 1) / (t * Real.log t) ^ 2) := by
      rw [thetaErrorKernel, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg (by linarith : 0 ≤ Real.log t + 1),
        abs_of_nonneg (sq_nonneg (t * Real.log t))]
      ring
    _ ≤ (515 * t / Real.log t ^ 3) * (2 / (t ^ 2 * Real.log t)) :=
      mul_le_mul he hf' hf (by positivity)
    _ = (1030 / Real.log t ^ 2) * (t⁻¹ / Real.log t ^ 2) := by
      field_simp
      ring
    _ ≤ (1030 / Real.log x ^ 2) * (t⁻¹ / Real.log t ^ 2) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)

theorem reciprocal_prime_error_le_log_cube {n : ℕ}
    (hn : 2 * Real.exp 100 ≤ Real.log (n : ℝ)) :
    |primeReciprocalSum n - (Real.log (Real.log n) + mertensSecondConstant)| ≤
      1545 / Real.log (n : ℝ) ^ 3 := by
  have hL := log_large_of_tail hn
  have hn0 : (0 : ℝ) < n := by
    by_contra! hz
    have hnz : n = 0 := by exact_mod_cast (le_antisymm hz (Nat.cast_nonneg n))
    subst n
    norm_num at hL
  have hn2 : (2 : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos hn0
    linarith
  have he := mertensSecond_error_decomposition hn2
  rw [Nat.floor_natCast] at he
  rw [he]
  have htheta := theta_error_le_log_cube hn0 hn
  have hend : |(Chebyshev.theta n - n) / ((n : ℝ) * Real.log n)| ≤
      515 / Real.log (n : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) * Real.log n)]
    apply (div_le_iff₀ (by positivity)).mpr
    apply htheta.trans
    have h : (1 : ℝ) ≤ Real.log n := by linarith
    have hm := mul_le_mul_of_nonneg_left h
      (by positivity : 0 ≤ 515 * (n : ℝ) / Real.log n ^ 3)
    convert hm using 1 <;> ring
  have hint := theta_error_integral_le_log_cube hn0 hn
  rw [Real.norm_eq_abs] at hint
  have htri : |(Chebyshev.theta n - n) / ((n : ℝ) * Real.log n) -
      ∫ t in Ioi (n : ℝ), thetaErrorKernel t| ≤
      |(Chebyshev.theta n - n) / ((n : ℝ) * Real.log n)| +
        |∫ t in Ioi (n : ℝ), thetaErrorKernel t| := by
    simpa using abs_sub_le ((Chebyshev.theta n - n) / ((n : ℝ) * Real.log n))
      0 (∫ t in Ioi (n : ℝ), thetaErrorKernel t)
  exact (htri.trans (add_le_add hend hint)).trans_eq (by ring)

theorem log_primeProduct_error_le_log_cube {n : ℕ}
    (hn : 2 * Real.exp 100 ≤ Real.log (n : ℝ)) :
    |Real.log (primeProduct n) + Real.log (Real.log n) +
      Real.eulerMascheroniConstant| ≤ 1547 / Real.log (n : ℝ) ^ 3 := by
  have hL := log_large_of_tail hn
  have hn0 : (0 : ℝ) < n := by
    by_contra! hz
    have hnz : n = 0 := by exact_mod_cast (le_antisymm hz (Nat.cast_nonneg n))
    subst n
    norm_num at hL
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by
    have := Real.log_le_sub_one_of_pos hn0
    linarith)
  have hpow : Real.log (n : ℝ) ^ 3 ≤ n := by
    have h := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ Real.log (n : ℝ)) 5
    norm_num [Finset.sum_range_succ, Nat.factorial, Real.exp_log hn0] at h
    have hp := mul_le_mul_of_nonneg_right hL
      (pow_nonneg (by linarith : 0 ≤ Real.log (n : ℝ)) 3)
    nlinarith
  rw [← mertensConstant_eq_eulerMascheroni, log_primeProduct_error_eq]
  have herr := reciprocal_prime_error_le_log_cube hn
  have hcorr := logarithmicCorrection_tail_norm_le_div n hn1
  rw [Real.norm_eq_abs] at hcorr
  have hc : |logarithmicCorrectionLimit - logarithmicCorrection n| ≤
      2 / Real.log (n : ℝ) ^ 3 :=
    hcorr.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow)
  have h := abs_add_le
    (-(primeReciprocalSum n - (Real.log (Real.log n) + mertensSecondConstant)))
    (logarithmicCorrectionLimit - logarithmicCorrection n)
  rw [abs_neg] at h
  exact (h.trans (add_le_add herr hc)).trans_eq (by ring)

#print axioms theta_error_integral_le_log_cube
#print axioms reciprocal_prime_error_le_log_cube
#print axioms log_primeProduct_error_le_log_cube

end LiuWang.Proof.Campaign20260915.Totient
