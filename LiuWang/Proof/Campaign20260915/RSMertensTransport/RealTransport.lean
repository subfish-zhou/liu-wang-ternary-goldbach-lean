import AnalyticNumberTheory.Mertens.Theorems

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.Mertens
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.RSMertensTransport

theorem mem_primesUpTo_floor {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesUpTo ⌊x⌋₊ ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  rw [mem_primesUpTo, Nat.le_floor_iff hx]

theorem floor_lt_prime_iff {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    ⌊x⌋₊ < p ↔ x < (p : ℝ) :=
  Nat.floor_lt hx

theorem logarithmicCorrectionTerm_nonneg (p : ℕ) :
    0 ≤ logarithmicCorrectionTerm p := by
  unfold logarithmicCorrectionTerm
  split_ifs with hp
  · have h := Real.log_le_sub_one_of_pos (primeFactor_pos hp)
    linarith
  · rfl

theorem logarithmicCorrection_tail_nonneg (n : ℕ) :
    0 ≤ logarithmicCorrectionLimit - logarithmicCorrection n := by
  rw [logarithmicCorrectionLimit_sub_eq_tail]
  exact tsum_nonneg fun k => logarithmicCorrectionTerm_nonneg _

theorem logarithmicCorrection_tail_abs (n : ℕ) :
    |logarithmicCorrectionLimit - logarithmicCorrection n| =
      logarithmicCorrectionLimit - logarithmicCorrection n :=
  abs_of_nonneg (logarithmicCorrection_tail_nonneg n)

theorem logarithmicCorrection_tail_eq_real_shift (x : ℝ) :
    logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊ =
      ∑' k : ℕ, logarithmicCorrectionTerm (k + (⌊x⌋₊ + 1)) :=
  logarithmicCorrectionLimit_sub_eq_tail _

theorem log_primeProduct_error_eq_real (x : ℝ) :
    Real.log (primeProduct ⌊x⌋₊) + Real.log (Real.log x) +
        Real.eulerMascheroniConstant =
      -(primeReciprocalSum ⌊x⌋₊ -
          (Real.log (Real.log x) + mertensSecondConstant)) +
        (logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊) := by
  rw [← mertensConstant_eq_eulerMascheroni]
  have h := log_primeProduct_error_eq ⌊x⌋₊
  linarith

theorem log_primeProduct_error_eq_theta {x : ℝ} (hx : 2 ≤ x) :
    Real.log (primeProduct ⌊x⌋₊) + Real.log (Real.log x) +
        Real.eulerMascheroniConstant =
      -(Chebyshev.theta x - x) / (x * Real.log x) +
        (∫ t in Ioi x, thetaErrorKernel t) +
        (logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊) := by
  rw [log_primeProduct_error_eq_real, mertensSecond_error_decomposition hx]
  ring

theorem primeProduct_eq_exp_reciprocal_error {x : ℝ} (hx : 1 < x) :
    primeProduct ⌊x⌋₊ =
      Real.exp (-Real.eulerMascheroniConstant) / Real.log x *
        Real.exp (-(primeReciprocalSum ⌊x⌋₊ -
            (Real.log (Real.log x) + mertensSecondConstant)) +
          (logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊)) := by
  rw [← log_primeProduct_error_eq_real, Real.exp_add, Real.exp_add,
    Real.exp_log (primeProduct_pos _), Real.exp_log (Real.log_pos hx)]
  have hcancel : Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  field_simp [(Real.log_pos hx).ne']
  rw [mul_assoc, hcancel, mul_one]

theorem reciprocal_prime_error_floor_transport {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ -
        (Real.log (Real.log x) + mertensSecondConstant) =
      (primeReciprocalSum ⌊x⌋₊ -
        (Real.log (Real.log (⌊x⌋₊ : ℝ)) + mertensSecondConstant)) -
      Real.log (Real.log x / Real.log (⌊x⌋₊ : ℝ)) := by
  have hn : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (Nat.le_floor hx)
  have hlogn : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.log_div hlogx.ne' hlogn.ne']
  ring

theorem log_primeProduct_error_floor_transport {x : ℝ} (hx : 2 ≤ x) :
    Real.log (primeProduct ⌊x⌋₊) + Real.log (Real.log x) +
        Real.eulerMascheroniConstant =
      (Real.log (primeProduct ⌊x⌋₊) +
        Real.log (Real.log (⌊x⌋₊ : ℝ)) + Real.eulerMascheroniConstant) +
      Real.log (Real.log x / Real.log (⌊x⌋₊ : ℝ)) := by
  have hreal := log_primeProduct_error_eq_real x
  have hnat := log_primeProduct_error_eq_real (⌊x⌋₊ : ℝ)
  rw [Nat.floor_natCast] at hnat
  have htransport := reciprocal_prime_error_floor_transport hx
  linarith

theorem log_log_floor_transport_nonneg {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ Real.log (Real.log x / Real.log (⌊x⌋₊ : ℝ)) := by
  have hn : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (Nat.le_floor hx)
  have hn0 : 0 < (⌊x⌋₊ : ℝ) := by linarith
  apply Real.log_nonneg
  exact (le_div_iff₀ (Real.log_pos (by linarith : (1 : ℝ) < ⌊x⌋₊))).mpr
    (by simpa using Real.log_le_log hn0 (Nat.floor_le (by linarith : 0 ≤ x)))

#print axioms log_primeProduct_error_eq_theta
#print axioms primeProduct_eq_exp_reciprocal_error
#print axioms reciprocal_prime_error_floor_transport
#print axioms log_primeProduct_error_floor_transport
#print axioms logarithmicCorrection_tail_nonneg

end LiuWang.Proof.Campaign20260915.RSMertensTransport
