import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalC2Witness

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaWinding

def sourceHorizontalGeometricWeight (T x : ℝ) : ℝ :=
  Real.log ‖sourceStripNormalizer (horizontalAt T x)‖ -
    Real.log ‖horizontalAt T x - 1‖ -
    (5 / 4 - x) / 3 * Real.log T + sourceBottomLogWeight T x

def sourceExactHorizontalLogBudget (T : ℝ) : ℝ :=
  (∫ x in (1 / 2 : ℝ)..(5 / 4),
    Real.log (sourceStripNormEnvelope (horizontalAt T x))) + realLogTail (5 / 4)

theorem sourceStripLogEnvelope_eq_geometricWeight {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    Real.log (sourceStripNormEnvelope (horizontalAt T x)) =
      ((sourceStripBoundaryExponent (horizontalAt T x)).re +
        (5 / 4 - x) / 3 * Real.log T) + sourceHorizontalGeometricWeight T x := by
  have hD := norm_ne_zero_iff.mpr (sourceStripNormalizer_ne_zero (horizontalAt T x))
  have hE := norm_ne_zero_iff.mpr (sourceBottomBarrier_ne_zero (horizontalAt T x))
  have hS : ‖horizontalAt T x - 1‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have hi := congrArg Complex.im h
    simp [horizontalAt] at hi
    exact hT hi
  rw [sourceStripNormEnvelope,
    Real.log_div (mul_ne_zero (mul_ne_zero hD (Real.exp_ne_zero _)) hE) hS,
    Real.log_mul (mul_ne_zero hD (Real.exp_ne_zero _)) hE,
    Real.log_mul hD (Real.exp_ne_zero _), Real.log_exp,
    sourceBottomBarrier_norm, Real.log_exp]
  simp only [horizontalAt, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_self, add_zero, add_im, mul_im, zero_add, mul_one]
  unfold sourceHorizontalGeometricWeight horizontalAt
  ring

theorem sourceHorizontalGeometricWeight_eq_radial {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    sourceHorizontalGeometricWeight T x =
      ((17 / 12 - x / 3) * Real.log (‖horizontalAt T x‖ / T) -
        Real.log (‖horizontalAt T x - 1‖ / T)) +
          sourceStripArgumentCorrection T x + sourceBottomLogWeight T x := by
  have hs : 0 < (horizontalAt T x).re := by simpa [horizontalAt] using hx
  have hi : 0 < (horizontalAt T x).im := by simpa [horizontalAt] using hT
  have hn : 0 < ‖horizontalAt T x‖ := by
    apply norm_pos_iff.mpr
    intro h
    simp [h] at hi
  have hn1 : 0 < ‖horizontalAt T x - 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he := congrArg Complex.im h
    simp [horizontalAt] at he
    linarith
  rw [sourceHorizontalGeometricWeight, sourceStripNormalizer_norm hs hi,
    Real.log_mul (Real.rpow_pos_of_pos hn _).ne' (Real.exp_ne_zero _),
    Real.log_rpow hn, Real.log_exp,
    Real.log_div hn.ne' hT.ne', Real.log_div hn1.ne' hT.ne']
  simp only [horizontalAt, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_self, add_zero, add_im, mul_im, zero_add, mul_one]
  ring

theorem sourceHorizontalGeometricWeight_intervalIntegrable {T : ℝ} (hT : 0 < T) :
    IntervalIntegrable (sourceHorizontalGeometricWeight T) volume (1 / 2) (5 / 4) := by
  have hf : Continuous (fun x : ℝ =>
      (sourceStripBoundaryExponent (horizontalAt T x)).re +
        (5 / 4 - x) / 3 * Real.log T) := by
    simp_rw [sourceStripBoundaryExponent_re]
    unfold horizontalAt
    fun_prop
  apply ((sourceStripLogEnvelope_intervalIntegrable hT).sub
    (hf.intervalIntegrable _ _)).congr
  intro x _
  have h := sourceStripLogEnvelope_eq_geometricWeight hT.ne' x
  dsimp only
  linarith

theorem integral_sourceStrip_affineWeight (T : ℝ) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4),
      (sourceStripBoundaryExponent (horizontalAt T x)).re +
        (5 / 4 - x) / 3 * Real.log T) =
      3 / 8 * (Real.log (253 / 100 : ℝ) + realLogZeta (5 / 4)) +
        3 / 32 * Real.log T := by
  have he (x : ℝ) :
      (sourceStripBoundaryExponent (horizontalAt T x)).re +
        (5 / 4 - x) / 3 * Real.log T =
      (5 / 3 * Real.log (253 / 100) - 2 / 3 * realLogZeta (5 / 4) +
        5 / 12 * Real.log T) +
      x * (-4 / 3 * Real.log (253 / 100) + 4 / 3 * realLogZeta (5 / 4) -
        Real.log T / 3) := by
    rw [sourceStripBoundaryExponent_re]
    simp [horizontalAt]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous (fun x : ℝ =>
      x * (-4 / 3 * Real.log (253 / 100) + 4 / 3 * realLogZeta (5 / 4) -
        Real.log T / 3))).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
  norm_num
  ring

theorem sourceExactHorizontalLogBudget_decomposition {T : ℝ} (hT : 0 < T) :
    sourceExactHorizontalLogBudget T =
      realLogTail (5 / 4) +
        3 / 8 * (Real.log (253 / 100 : ℝ) + realLogZeta (5 / 4)) +
        3 / 32 * Real.log T +
          ∫ x in (1 / 2 : ℝ)..(5 / 4), sourceHorizontalGeometricWeight T x := by
  have hf : Continuous (fun x : ℝ =>
      (sourceStripBoundaryExponent (horizontalAt T x)).re +
        (5 / 4 - x) / 3 * Real.log T) := by
    simp_rw [sourceStripBoundaryExponent_re]
    unfold horizontalAt
    fun_prop
  unfold sourceExactHorizontalLogBudget
  simp_rw [sourceStripLogEnvelope_eq_geometricWeight hT.ne']
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _)
    (sourceHorizontalGeometricWeight_intervalIntegrable hT),
    integral_sourceStrip_affineWeight]
  ring

theorem sourceExactHorizontalLogBudget_le_numeric (T : ℝ) :
    sourceExactHorizontalLogBudget T ≤ sourceHorizontalLogBudget T := by
  unfold sourceExactHorizontalLogBudget sourceHorizontalLogBudget
  linarith [realLogTail_fiveFourths_upper]

theorem sourceExactHorizontalLogBudget_sub_shift_upper {T : ℝ} (hT : 0 < T) :
    sourceExactHorizontalLogBudget T - unitShiftRealBudget ≤
      (35219 / 10000 : ℝ) + 3 / 32 * Real.log T +
        ∫ x in (1 / 2 : ℝ)..(5 / 4), sourceHorizontalGeometricWeight T x := by
  rw [sourceExactHorizontalLogBudget_decomposition hT]
  linarith [source_real_integral_budget_upper]

theorem horizontalLogMass_exactBudget_C2_witness {T : ℝ} (hT : 128 * Real.pi ≤ T)
    (hbad : sourceExactHorizontalLogBudget T < horizontalLogMass T) :
    ∃ eta : ℝ, 8 < eta ∧ (∀ k : ℤ, eta ≠ k) ∧
      2 < |sourceSevenNormalized eta ⌊eta⌋₊| + |sourceJnNormalized eta| +
        |sourcePolynomialExteriorNormalized eta| + |sourceLeftNormalized eta| +
          |sourceRightNormalized eta| := by
  have ht : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hu := horizontalLogMass_real_tail_upper ht.ne' (by norm_num : (1 : ℝ) < 5 / 4)
  have hI :
      (∫ x in (1 / 2 : ℝ)..(5 / 4),
        Real.log (sourceStripNormEnvelope (horizontalAt T x))) <
      ∫ x in (1 / 2 : ℝ)..(5 / 4), Real.log ‖riemannZeta (horizontalAt T x)‖ := by
    unfold sourceExactHorizontalLogBudget at hbad
    linarith
  obtain ⟨t, ht, h⟩ := sourceStrip_integral_violation_critical_witness hT hI
  exact criticalGrowth_seven_C2_witness ht h

theorem horizontalLogMass_affineGeometry_C2_witness {T : ℝ} (hT : 128 * Real.pi ≤ T)
    (hbad : (35219 / 10000 : ℝ) + 3 / 32 * Real.log T +
      (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceHorizontalGeometricWeight T x) <
        horizontalLogMass T - unitShiftRealBudget) :
    ∃ eta : ℝ, 8 < eta ∧ (∀ k : ℤ, eta ≠ k) ∧
      2 < |sourceSevenNormalized eta ⌊eta⌋₊| + |sourceJnNormalized eta| +
        |sourcePolynomialExteriorNormalized eta| + |sourceLeftNormalized eta| +
          |sourceRightNormalized eta| := by
  apply horizontalLogMass_exactBudget_C2_witness hT
  have ht : 0 < T := lt_of_lt_of_le (by positivity) hT
  linarith [sourceExactHorizontalLogBudget_sub_shift_upper ht]

#print axioms sourceStripLogEnvelope_eq_geometricWeight
#print axioms sourceHorizontalGeometricWeight_eq_radial
#print axioms sourceExactHorizontalLogBudget_decomposition
#print axioms sourceExactHorizontalLogBudget_sub_shift_upper
#print axioms horizontalLogMass_exactBudget_C2_witness
#print axioms horizontalLogMass_affineGeometry_C2_witness

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
