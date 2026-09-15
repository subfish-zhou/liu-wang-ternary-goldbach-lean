import LiuWang.Proof.Campaign20260915.RSMertensTransport.ProductCancellation

/-! Actual real-parameter Euler product error and downstream cancellation.
Theorem 9 and Lemma 13 numerical inputs remain explicit in the conditional consumers.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open AnalyticNumberTheory.Mertens MeasureTheory Set
namespace LiuWang.Proof.Campaign20260915.Parent.MertensTransportAudit
open LiuWang.Proof.Campaign20260915.RSMertensTransport

theorem actual_product_theta_error {x : ℝ} (hx : 2 ≤ x) :
    Real.log (primeProduct ⌊x⌋₊) + Real.log (Real.log x) +
        Real.eulerMascheroniConstant =
      -(Chebyshev.theta x - x) / (x * Real.log x) +
        (∫ t in Ioi x, thetaErrorKernel t) +
        (logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊) :=
  log_primeProduct_error_eq_theta hx

#print axioms actual_product_theta_error
end LiuWang.Proof.Campaign20260915.Parent.MertensTransportAudit

#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.mem_primesUpTo_floor
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.floor_lt_prime_iff
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrectionTerm_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_abs
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_eq_real_shift
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.log_primeProduct_error_eq_real
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.log_primeProduct_error_eq_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.primeProduct_eq_exp_reciprocal_error
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.reciprocal_prime_error_floor_transport
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.log_primeProduct_error_floor_transport
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.log_log_floor_transport_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.hasSum_logarithmicCorrection_prime
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_prime_le
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_prime_le_weighted_square
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.prime_log_square_window_eq
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.prime_log_square_window_le
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_window_eq
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_window_le_of_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_le_of_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_le_original_of_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_norm_le_original_of_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_eq_prime_tsum
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_eq_prime_power_tsum
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.original_signed_log_tail_eq
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.original_signed_log_tail_bounds_of_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.logarithmicCorrection_tail_lt_original_of_theorem9
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.log_primeProduct_upper_of_lemma13_and_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.primeProduct_upper_of_lemma13_and_theta
#print axioms LiuWang.Proof.Campaign20260915.RSMertensTransport.inv_primeProduct_upper_of_lemma13
