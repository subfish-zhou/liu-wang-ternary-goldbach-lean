import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.EndpointBounds
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.ProfileEnclosure

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

theorem endpoint_derivative_interval (j : PureKind) (b : Bool) :
    derivativeLo j (endpoint j b) (endpointLogLo j b) (endpointLogHi j b) (endpointExpLo j b) ≤
        profileLogDerivative j 3100 (endpoint j b) ∧
      profileLogDerivative j 3100 (endpoint j b) ≤
        derivativeHi j (endpoint j b) (endpointLogLo j b) (endpointLogHi j b) (endpointExpHi j b) := by
  apply derivative_interval
  · cases j <;> cases b <;> norm_num [endpoint]
  · cases j <;> cases b <;> norm_num [endpointLogLo]
  · cases j <;> cases b <;> norm_num [endpointExpLo]
  · exact (endpoint_log_bounds j b).1
  · exact (endpoint_log_bounds j b).2
  · exact endpoint_exp_bounds j b
  · cases j <;> cases b <;> norm_num [nuDLo, endpoint, endpointLogLo]

theorem derivative_bracket_signs (j : PureKind) :
    0 < profileLogDerivative j 3100 (endpoint j false) ∧
      profileLogDerivative j 3100 (endpoint j true) < 0 := by
  constructor
  · apply lt_of_lt_of_le _ (endpoint_derivative_interval j false).1
    cases j <;>
      norm_num [derivativeLo, nuDLo, nuHi, scaleLo, zeroPower, decayPower,
        endpoint, endpointLogLo, endpointLogHi, endpointExpLo]
  · apply lt_of_le_of_lt (endpoint_derivative_interval j true).2
    cases j <;>
      norm_num [derivativeHi, nuDHi, nuLo, scaleHi, zeroPower, decayPower,
        endpoint, endpointLogLo, endpointLogHi, endpointExpHi]

theorem criticalPoint_in_bracket (j : PureKind) :
    endpoint j false < criticalPoint j ∧ criticalPoint j < endpoint j true := by
  have hc := criticalPoint_spec j
  have hd := endpoint_domain j
  have hs := derivative_bracket_signs j
  have hm := (profileLogDerivative_strictAnti j (by norm_num : (0 : ℝ) < 3100)).antitoneOn
  constructor
  · by_contra h
    have hle : criticalPoint j ≤ endpoint j false := le_of_not_gt h
    have hh := hm hc.1.1.le hd.1.le hle
    rw [hc.2] at hh
    linarith [hs.1]
  · by_contra h
    have hle : endpoint j true ≤ criticalPoint j := le_of_not_gt h
    have hh := hm (hd.1.le.trans hd.2.1.le) hc.1.1.le hle
    rw [hc.2] at hh
    linarith [hs.2]

theorem entire_bracket_bound (j : PureKind) {t : ℝ}
    (ht : t ∈ Set.Icc (endpoint j false) (endpoint j true)) :
    conductorProfile j 3100 t ≤ certifiedValue j := by
  have hd := endpoint_domain j
  have h := profile_bracket_bound j
    (a := endpoint j false) (b := endpoint j true)
    (ll := endpointLogLo j false) (lh := endpointLogHi j true)
    (eh := endpointExpHi j false) (el := endpointExpLo j true)
    (z := finalArgument j) (by linarith [hd.1]) hd.2.1.le
    (by cases j <;> norm_num [endpointLogLo])
    (endpoint_log_bounds j false).1 (endpoint_log_bounds j true).2
    (endpoint_exp_bounds j false).2 (by cases j <;> norm_num [endpointExpLo])
    (endpoint_exp_bounds j true).1
    (by cases j <;> norm_num [scaleLo, zeroPower, endpointExpLo, endpoint, finalArgument])
    ht.1 ht.2
  apply h.trans
  apply le_trans (mul_le_mul_of_nonneg_left (final_exp_bound j)
    (by cases j <;> norm_num [endpointExpHi, nuHi, endpointLogLo, endpointLogHi]))
  cases j <;>
    norm_num [endpointExpHi, nuHi, endpointLogLo, endpointLogHi, finalExpHi, certifiedValue]

theorem criticalValue_certified (j : PureKind) : criticalValue j ≤ certifiedValue j :=
  entire_bracket_bound j
    ⟨(criticalPoint_in_bracket j).1.le, (criticalPoint_in_bracket j).2.le⟩

theorem criticalValue_original (j : PureKind) : criticalValue j ≤ sourceScalarBudget j := by
  have h := certifiedValue_budget j
  exact (criticalValue_certified j).trans (by linarith [h.1, h.2])

theorem criticalValue_linear : criticalValue .linear ≤ 0.0000025636 :=
  criticalValue_original .linear

theorem criticalValue_quadratic : criticalValue .quadratic ≤ 0.00013 :=
  criticalValue_original .quadratic

theorem criticalValue_cubic : criticalValue .cubic ≤ 0.028 :=
  criticalValue_original .cubic

theorem paper_scalar_bound (j : PureKind) {r L : ℝ} (h : paperDomain r L) :
    conductorScalar j r L ≤ sourceScalarBudget j :=
  (original_scalar_bound_iff j).mpr (criticalValue_original j) r L h

theorem paper_scalar_stronger (j : PureKind) {r L : ℝ} (h : paperDomain r L) :
    conductorScalar j r L ≤ certifiedValue j := by
  have hc := criticalPoint_spec j
  exact (scalar_critical_reduction j hc.1 hc.2 h.1 h.2.1).trans (criticalValue_certified j)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
