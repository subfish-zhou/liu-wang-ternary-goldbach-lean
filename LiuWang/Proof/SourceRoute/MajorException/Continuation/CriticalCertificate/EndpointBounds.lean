import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.NumericData

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

theorem endpoint_log_bounds (j : PureKind) (b : Bool) :
    endpointLogLo j b ≤ Real.log (endpoint j b) ∧
      Real.log (endpoint j b) ≤ endpointLogHi j b := by
  apply log_scaled_bounds
  · cases j <;> cases b <;> norm_num [endpoint]
  · cases j <;> cases b <;> norm_num [endpoint]
  · cases j <;> cases b <;>
      norm_num [endpoint, endpointLogLo, logPoly, logError, sum_range_succ]
  · cases j <;> cases b <;>
      norm_num [endpoint, endpointLogHi, logPoly, logError, sum_range_succ]

theorem endpoint_exp_bounds (j : PureKind) (b : Bool) :
    endpointExpLo j b ≤ Real.exp (-endpoint j b/16) ∧
      Real.exp (-endpoint j b/16) ≤ endpointExpHi j b := by
  apply exp_small_bounds
  · cases j <;> cases b <;> norm_num [endpoint]
  · cases j <;> cases b <;>
      norm_num [endpoint, endpointExpLo, expPoly, expError, sum_range_succ]
  · cases j <;> cases b <;>
      norm_num [endpoint, endpointExpHi, expPoly, expError, sum_range_succ]

theorem final_exp_bound (j : PureKind) :
    Real.exp (finalArgument j) ≤ (finalExpHi j)^4 := by
  have h : (0 : ℝ) ≤ Real.exp (finalArgument j/4) ∧
      Real.exp (finalArgument j/4) ≤ finalExpHi j := by
    apply exp_small_bounds
    · cases j <;> norm_num [finalArgument]
    · cases j <;> norm_num [finalArgument, expPoly, expError, sum_range_succ]
    · cases j <;> norm_num [finalArgument, finalExpHi, expPoly, expError, sum_range_succ]
  have hh := (exp_nat_scale (m := 4) (by norm_num) h).2
  simpa only [Nat.cast_ofNat, show 4*(finalArgument j/4) = finalArgument j by ring] using hh

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
