import LiuWang.Proof.Campaign20260915.RSMertensTransport.OriginalTail

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.Mertens

namespace LiuWang.Proof.Campaign20260915.RSMertensTransport

theorem logarithmicCorrection_tail_lt_original_of_theorem9 {x : ℝ}
    (hx : 1 < x)
    (htheta : ∀ t ∈ Set.Ici x, Chebyshev.theta t < 1.01624 * t) :
    logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊ <
      1.02 / ((x - 1) * Real.log x) := by
  have hxl := Real.log_pos hx
  have hxm : 0 < x - 1 := by linarith
  exact (logarithmicCorrection_tail_le_of_theta hx (by norm_num : (0 : ℝ) ≤ 1.01624)
    (fun t ht => (htheta t ht).le)).trans_lt
      (div_lt_div_of_pos_right (by norm_num) (by positivity))

/-- This consumes, but does not prove, the original Lemma 13 input. -/
theorem log_primeProduct_upper_of_lemma13_and_theta {x : ℝ} (hx : 1 < x)
    (htheta : ∀ t ∈ Set.Ici x, Chebyshev.theta t ≤ 1.02 * t)
    (hlemma13 :
      |primeReciprocalSum ⌊x⌋₊ - (Real.log (Real.log x) + mertensSecondConstant)| <
        Real.log (1 + 1 / (2 * Real.log x ^ 2)) -
          1.02 / ((x - 1) * Real.log x)) :
    Real.log (primeProduct ⌊x⌋₊) + Real.log (Real.log x) +
      Real.eulerMascheroniConstant < Real.log (1 + 1 / (2 * Real.log x ^ 2)) := by
  have htail := (logarithmicCorrection_tail_le_original_of_theta hx htheta).2
  have hlower := (abs_lt.mp hlemma13).1
  rw [log_primeProduct_error_eq_real]
  linarith

theorem primeProduct_upper_of_lemma13_and_theta {x : ℝ} (hx : 1 < x)
    (htheta : ∀ t ∈ Set.Ici x, Chebyshev.theta t ≤ 1.02 * t)
    (hlemma13 :
      |primeReciprocalSum ⌊x⌋₊ - (Real.log (Real.log x) + mertensSecondConstant)| <
        Real.log (1 + 1 / (2 * Real.log x ^ 2)) -
          1.02 / ((x - 1) * Real.log x)) :
    primeProduct ⌊x⌋₊ <
      Real.exp (-Real.eulerMascheroniConstant) / Real.log x *
        (1 + 1 / (2 * Real.log x ^ 2)) := by
  have hxl := Real.log_pos hx
  have ha : 0 < 1 + 1 / (2 * Real.log x ^ 2) := by positivity
  have hbase : 0 < Real.exp (-Real.eulerMascheroniConstant) / Real.log x := by
    positivity
  rw [primeProduct_eq_exp_reciprocal_error hx]
  apply mul_lt_mul_of_pos_left _ hbase
  rw [← Real.exp_log ha]
  apply Real.exp_lt_exp.mpr
  rw [← log_primeProduct_error_eq_real]
  exact log_primeProduct_upper_of_lemma13_and_theta hx htheta hlemma13

theorem inv_primeProduct_upper_of_lemma13 {x : ℝ} (hx : 1 < x)
    (hlemma13 :
      |primeReciprocalSum ⌊x⌋₊ - (Real.log (Real.log x) + mertensSecondConstant)| <
        Real.log (1 + 1 / (2 * Real.log x ^ 2)) -
          1.02 / ((x - 1) * Real.log x)) :
    (primeProduct ⌊x⌋₊)⁻¹ <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * Real.log x ^ 2)) := by
  have hxl := Real.log_pos hx
  have hxm : 0 < x - 1 := by linarith
  have hD : 0 ≤ 1.02 / ((x - 1) * Real.log x) := by positivity
  have htail := logarithmicCorrection_tail_nonneg ⌊x⌋₊
  have hupper := (abs_lt.mp hlemma13).2
  have herr := log_primeProduct_error_eq_real x
  have hl : -Real.log (primeProduct ⌊x⌋₊) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * Real.log x ^ 2)) := by linarith
  have he := Real.exp_lt_exp.mpr hl
  rwa [Real.exp_neg, Real.exp_log (primeProduct_pos _),
    Real.exp_add, Real.exp_add, Real.exp_log hxl,
    Real.exp_log (by positivity : 0 < 1 + 1 / (2 * Real.log x ^ 2))] at he

#print axioms logarithmicCorrection_tail_lt_original_of_theorem9
#print axioms log_primeProduct_upper_of_lemma13_and_theta
#print axioms primeProduct_upper_of_lemma13_and_theta
#print axioms inv_primeProduct_upper_of_lemma13

end LiuWang.Proof.Campaign20260915.RSMertensTransport
