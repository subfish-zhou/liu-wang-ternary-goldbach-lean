import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.StripGeometry

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaWinding

-- This is the logarithm of the source interpolation majorant, not a bound on zeta.
def originalStripLogEnvelope (T x : ℝ) : ℝ :=
  (5 / 4 - x) / (3 / 4) * Real.log (253 / 100) +
    (x - 1 / 2) / (3 / 4) * realLogZeta (5 / 4) +
    (1 + (5 / 4 - x) / 3) * Real.log ‖horizontalAt T x‖ -
    Real.log ‖horizontalAt T x - 1‖

def originalUpperFiniteConstant : ℝ :=
  3 / 8 * (Real.log (253 / 100) + realLogZeta (5 / 4)) +
    (∫ x in (5 / 4 : ℝ)..16, realLogZeta x) + 1 / 3000 + 1 / 500000

theorem originalStripLogEnvelope_decomposition (T x : ℝ) :
    originalStripLogEnvelope T x =
      (5 / 4 - x) / (3 / 4) * Real.log (253 / 100) +
        (x - 1 / 2) / (3 / 4) * realLogZeta (5 / 4) +
        (5 / 4 - x) / 3 * Real.log T + stripGeometryError T x := by
  unfold originalStripLogEnvelope stripGeometryError
  ring

theorem integral_originalStripLogEnvelope {T : ℝ} (hT : 0 < T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), originalStripLogEnvelope T x) =
      3 / 8 * (Real.log (253 / 100) + realLogZeta (5 / 4)) +
        3 / 32 * Real.log T +
        ∫ x in (1 / 2 : ℝ)..(5 / 4), stripGeometryError T x := by
  let f : ℝ → ℝ := fun x =>
    (5 / 4 - x) / (3 / 4) * Real.log (253 / 100) +
      (x - 1 / 2) / (3 / 4) * realLogZeta (5 / 4) +
      (5 / 4 - x) / 3 * Real.log T
  have hf : Continuous f := by dsimp [f]; fun_prop
  simp_rw [originalStripLogEnvelope_decomposition]
  change (∫ x in (1 / 2 : ℝ)..(5 / 4), f x + stripGeometryError T x) = _
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _)
    ((stripGeometryError_continuous hT.ne').intervalIntegrable _ _)]
  congr 1
  have he (x : ℝ) : f x =
      (5 / 3 * Real.log (253 / 100) - 2 / 3 * realLogZeta (5 / 4) +
        5 / 12 * Real.log T) +
      x * (-4 / 3 * Real.log (253 / 100) + 4 / 3 * realLogZeta (5 / 4) -
        Real.log T / 3) := by dsimp [f]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous (fun x : ℝ =>
      x * (-4 / 3 * Real.log (253 / 100) + 4 / 3 * realLogZeta (5 / 4) -
        Real.log T / 3))).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
  norm_num
  ring

theorem originalUpperEnvelope_finite_budget {T : ℝ} (hT : 168 * Real.pi < T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), originalStripLogEnvelope T x) +
      realLogTail (5 / 4) < originalUpperFiniteConstant + 3 / 32 * Real.log T := by
  have ht : 0 < T := lt_trans (by positivity) hT
  rw [integral_originalStripLogEnvelope ht,
    realLogTail_split (by norm_num : (1 : ℝ) < 5 / 4) (by norm_num : (1 : ℝ) < 16)]
  unfold originalUpperFiniteConstant
  linarith [integral_stripGeometryError_original_budget hT, realLogTail_sixteen_budget.2]

theorem original_log_coefficient_budget :
    ((3 / 32 : ℝ) + (37 / 25 - 1) / 2) / Real.pi < 57 / 500 := by
  rw [div_lt_iff₀ Real.pi_pos]
  linarith [Real.pi_gt_three]

#print axioms integral_originalStripLogEnvelope
#print axioms originalUpperEnvelope_finite_budget
#print axioms original_log_coefficient_budget

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
