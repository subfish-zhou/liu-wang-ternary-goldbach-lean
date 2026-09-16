import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.OriginalCriticalGrowth
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.StripGeometry
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.OriginalScalarBudget
import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanReferenceBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.PrincipalPsi.Quantitative
open BombieriVinogradov.SiegelWalfisz

theorem sourceHorizontalGeometricWeight_eq_stripGeometry {T x : ℝ}
    (hT : 0 < T) (hx : 0 < x) :
    sourceHorizontalGeometricWeight T x =
      stripGeometryError T x + sourceStripArgumentCorrection T x + sourceBottomLogWeight T x := by
  have hn : ‖horizontalAt T x‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have hi := congrArg Complex.im h
    simp [horizontalAt] at hi
    exact hT.ne' hi
  have hn1 : ‖horizontalAt T x - 1‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have hi := congrArg Complex.im h
    simp [horizontalAt] at hi
    exact hT.ne' hi
  rw [sourceHorizontalGeometricWeight_eq_radial hT hx,
    Real.log_div hn hT.ne', Real.log_div hn1 hT.ne']
  unfold stripGeometryError
  ring

theorem integral_sourceHorizontalGeometricWeight_original {T : ℝ}
    (hT : 168 * Real.pi < T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceHorizontalGeometricWeight T x) < 1 / 500000 := by
  have ht : 0 < T := lt_trans (by positivity) hT
  have hG : IntervalIntegrable (stripGeometryError T) volume (1 / 2) (5 / 4) :=
    (stripGeometryError_continuous ht.ne').intervalIntegrable _ _
  have hA : IntervalIntegrable (sourceStripArgumentCorrection T) volume (1 / 2) (5 / 4) :=
    (by unfold sourceStripArgumentCorrection; fun_prop :
      Continuous (sourceStripArgumentCorrection T)).intervalIntegrable _ _
  have hB : IntervalIntegrable (sourceBottomLogWeight T) volume (1 / 2) (5 / 4) :=
    (by unfold sourceBottomLogWeight; fun_prop :
      Continuous (sourceBottomLogWeight T)).intervalIntegrable _ _
  calc
    _ = ∫ x in (1 / 2 : ℝ)..(5 / 4),
        stripGeometryError T x + sourceStripArgumentCorrection T x + sourceBottomLogWeight T x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hx
      exact sourceHorizontalGeometricWeight_eq_stripGeometry ht (by linarith [hx.1])
    _ = (∫ x in (1 / 2 : ℝ)..(5 / 4), stripGeometryError T x) +
        (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceStripArgumentCorrection T x) +
        (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceBottomLogWeight T x) := by
      rw [intervalIntegral.integral_add (hG.add hA) hB,
        intervalIntegral.integral_add hG hA]
    _ < _ := by
      linarith [integral_stripGeometryError_le ht, sourceStrip_total_geometric_budget hT]

theorem horizontalLogMass_original_upper {T : ℝ} (hT : 168 * Real.pi < T) :
    horizontalLogMass T <
      realLogTail (5 / 4) + 3 / 8 * (Real.log (253 / 100 : ℝ) + realLogZeta (5 / 4)) +
        3 / 32 * Real.log T + 1 / 500000 := by
  have ht : 0 < T := lt_trans (by positivity) hT
  have hu := horizontalLogMass_exact_original_upper
    (by linarith [Real.pi_pos] : 128 * Real.pi ≤ T)
  rw [sourceExactHorizontalLogBudget_decomposition ht] at hu
  linarith [integral_sourceHorizontalGeometricWeight_original hT]

theorem horizontalLogMass_original_numeric_upper {T : ℝ} (hT : 168 * Real.pi < T) :
    horizontalLogMass T - unitShiftRealBudget <
      (35219 / 10000 : ℝ) + 3 / 32 * Real.log T + 1 / 500000 := by
  linarith [horizontalLogMass_original_upper hT, source_real_integral_budget_upper]

theorem horizontalLogMass_original_two_sided {T : ℝ} (hT : 168 * Real.pi < T) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2), Real.log ‖riemannZeta (horizontalAt T x) /
      riemannZeta (horizontalAt T (x + 1))‖) + unitShiftRealBudget ≤ horizontalLogMass T ∧
    horizontalLogMass T <
      realLogTail (5 / 4) + 3 / 8 * (Real.log (253 / 100 : ℝ) + realLogZeta (5 / 4)) +
        3 / 32 * Real.log T + 1 / 500000 :=
  ⟨horizontalLogMass_unitShift_lower (lt_trans (by positivity) hT).ne',
    horizontalLogMass_original_upper hT⟩

theorem original_two_height_log_budget {a b : ℝ}
    (ha : 168 * Real.pi < a) (hab : a ≤ b) :
    (horizontalLogMass b - unitShiftRealBudget +
      (37 / 25 : ℝ) * (∑' p : RiemannXiDivisorZeroIndex,
        (1 / (horizontalAt a (3 / 2) - riemannXiDivisorZeroValue p)).re) +
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog a x) + Real.log Real.pi / 2) / Real.pi <
        (171 / 100 : ℝ) + 57 / 500 * Real.log b := by
  have ha0 : 0 < a := lt_trans (by positivity) ha
  have hb := lt_of_lt_of_le ha hab
  have hu := horizontalLogMass_original_upper hb
  have hr := lehman_reference_mass_upper ha
  have hg := (abs_lt.mp (lehmanGamma_original_budget ha)).2
  have hl := original_reference_gamma_log_identity ha0
  have hm := Real.log_le_log ha0 hab
  have hn : horizontalLogMass b - unitShiftRealBudget +
      (37 / 25 : ℝ) * (∑' p : RiemannXiDivisorZeroIndex,
        (1 / (horizontalAt a (3 / 2) - riemannXiDivisorZeroValue p)).re) +
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog a x) + Real.log Real.pi / 2 <
        originalTuringScalarConstant + ((3 / 32 : ℝ) + (37 / 25 - 1) / 2) * Real.log b := by
    unfold originalTuringScalarConstant
    linarith
  calc
    _ < (originalTuringScalarConstant +
        ((3 / 32 : ℝ) + (37 / 25 - 1) / 2) * Real.log b) / Real.pi :=
      (div_lt_div_iff_of_pos_right Real.pi_pos).mpr hn
    _ = originalTuringScalarConstant / Real.pi + originalTuringScalarSlope * Real.log b := by
      unfold originalTuringScalarSlope
      ring
    _ < _ := originalTuringScalar_affine_upper (by linarith [Real.pi_gt_three])

#print axioms integral_sourceHorizontalGeometricWeight_original
#print axioms horizontalLogMass_original_upper
#print axioms horizontalLogMass_original_numeric_upper
#print axioms horizontalLogMass_original_two_sided
#print axioms original_two_height_log_budget

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
