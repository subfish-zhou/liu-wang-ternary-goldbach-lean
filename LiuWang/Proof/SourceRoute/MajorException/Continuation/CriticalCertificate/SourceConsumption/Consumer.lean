import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.PurePayment
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Normalization

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

def totalMixedCost (N : ℕ) (j : MixedKind) : ℝ :=
  ∑ q ∈ denominators (sourceP N), selectedMixedCost N q j

theorem actual_mixed_integral_lower {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (j : MixedKind) :
    -totalMixedCost N j ≤ (mixedIntegral N j).re := by
  have h := Complex.re_le_norm (-mixedIntegral N j)
  simp only [Complex.neg_re, norm_neg] at h
  have hc := actual_mixed_integrals hN j
  change ‖mixedIntegral N j‖ ≤ totalMixedCost N j at hc
  linarith

theorem major_lower_with_actual_remaining_masses {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor) :
    0.56115411*(N : ℝ)^2+(ordinaryIntegral N).re-
      totalMixedCost N .oneEach-totalMixedCost N .oneExceptionalTwoRegular-
      totalMixedCost N .twoExceptionalOneRegular-
      6760*(N : ℝ)^2/sourceL N^4 ≤ (majorIntegral N).re := by
  have h := majorIntegral_source_lower hN hodd
  obtain ⟨hp1, hp2, hp3⟩ := actual_pure_integrals hN hq hr h987 hphi
  have hn1 := Complex.re_le_norm (-selectedPureIntegral N .linear)
  have hn2 := Complex.re_le_norm (-selectedPureIntegral N .quadratic)
  have hn3 := Complex.re_le_norm (-selectedPureIntegral N .cubic)
  simp only [Complex.neg_re, norm_neg] at hn1 hn2 hn3
  have hm1 := actual_mixed_integral_lower (exp_2000_le_of_exp_3100_le hN) .oneEach
  have hm2 := actual_mixed_integral_lower (exp_2000_le_of_exp_3100_le hN) .oneExceptionalTwoRegular
  have hm3 := actual_mixed_integral_lower (exp_2000_le_of_exp_3100_le hN) .twoExceptionalOneRegular
  linarith

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
