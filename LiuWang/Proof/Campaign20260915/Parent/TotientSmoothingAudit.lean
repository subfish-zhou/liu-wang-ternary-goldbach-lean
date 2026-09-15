import LiuWang.Proof.Campaign20260915.Totient.RSSmoothingAudit

/-! Parent consumption of actual all-order desmoothing and the all-x first primitive.
The complete higher-order spectral assembly and original effective budgets are not asserted.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.Parent.TotientSmoothingAudit
open LiuWang.Proof.Campaign20260915.Totient

theorem actual_psi_desmoothing {m : ℕ} {δ a x : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hcut : 1 + (m : ℝ) * δ * a < a)
    (hax : a ≤ x) :
    1 < x - (m : ℝ) * (δ * x) ∧
      (fwdDiff (δ * x))^[m] (rsPsiPrimitive m) (x - (m : ℝ) * (δ * x)) /
        (δ * x) ^ m ≤ Chebyshev.psi x ∧
      Chebyshev.psi x ≤
        (fwdDiff (δ * x))^[m] (rsPsiPrimitive m) x / (δ * x) ^ m :=
  rsPsiPrimitive_original_desmoothing hδ ha hcut hax

theorem actual_first_primitive_spectral {x : ℝ} (hx : 1 < x) :
    (rsPsiPrimitive 1 x : ℂ) =
      ((1 - Real.log (2 * Real.pi) : ℝ) : ℂ) * ((x : ℂ) - 1) +
      ((x : ℂ) - 1) ^ 2 / 2 -
      ((∑' p, rsZeroPrimitive 1 x p) - ∑' p, rsZeroPrimitive 1 1 p) +
      gammaCorrection x :=
  rsPsiPrimitive_one_spectral hx

#print axioms actual_psi_desmoothing
#print axioms actual_first_primitive_spectral
end LiuWang.Proof.Campaign20260915.Parent.TotientSmoothingAudit

#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiBox_monotone
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiBox_bounds
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiBox_desmoothing
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiBox_original_domain
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiBox_original_desmoothing
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_integrable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_difference_integral
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_finite_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_original_desmoothing
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_deriv
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_zero_denominator_lower
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_shift_bound
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_difference_bound
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroMoment_summable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_summable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_iter_summable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_difference_tsum
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_sum_difference_bound
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_normalized_difference_bound
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsMainPrimitive_deriv
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsMainPrimitive_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsMainPrimitive_finite_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsMainPrimitive_normalized_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsMainPrimitive_original_two_sided
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_one_eq_integrated
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_one
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_integrated_formula_all
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_one_spectral
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_compact_bound
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroSum_continuousOn_Icc
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroSum_integral
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_norm_mono
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_backward_bound
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_sum_backward_bound
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroPrimitive_original_backward
