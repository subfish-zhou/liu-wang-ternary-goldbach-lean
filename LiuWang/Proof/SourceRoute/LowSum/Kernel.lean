import LiuWang.Proof.WeightedLowZeros.Weight
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros

namespace LiuWang.Proof.SourceRoute.LowSum

def coefficient (alpha : ℝ) : ℝ := (1 - (0.001 : ℝ) ^ alpha) / alpha

def coefficientSlope (alpha : ℝ) : ℝ :=
  ((0.001 : ℝ) ^ alpha * (1 - alpha * Real.log 0.001) - 1) / alpha ^ 2

def kernel (N : ℕ) (alpha : ℝ) : ℝ :=
  (N : ℝ) ^ (alpha - 1) * sourceL N * coefficient alpha

theorem coefficient_hasDerivAt {alpha : ℝ} (ha : 0 < alpha) :
    HasDerivAt coefficient (coefficientSlope alpha) alpha := by
  have h := (((hasDerivAt_id alpha).const_rpow
    (by norm_num : (0 : ℝ) < 0.001)).const_sub 1).div (hasDerivAt_id alpha) ha.ne'
  apply h.congr_deriv
  dsimp [coefficientSlope]
  ring

theorem coefficientSlope_nonpos (alpha : ℝ) : coefficientSlope alpha ≤ 0 := by
  have h := Real.add_one_le_exp (-Real.log (0.001 : ℝ) * alpha)
  have hp : 0 < (0.001 : ℝ) ^ alpha := Real.rpow_pos_of_pos (by norm_num) _
  have he : Real.exp (-Real.log (0.001 : ℝ) * alpha) * (0.001 : ℝ) ^ alpha = 1 := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hm := mul_le_mul_of_nonneg_right h hp.le
  rw [he] at hm
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)

theorem coefficient_antitone : AntitoneOn coefficient (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (coefficient_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (coefficient_hasDerivAt (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(coefficient_hasDerivAt (interior_subset hx)).deriv]
    exact coefficientSlope_nonpos x

theorem coefficient_nonneg {alpha : ℝ} (ha : 0 < alpha) : 0 ≤ coefficient alpha :=
  div_nonneg (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) ha.le)) ha.le

theorem continuousOn_kernel {N : ℕ} (hN : 0 < N) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (kernel N) (Set.Icc a b) := by
  intro x hx
  have hc := (coefficient_hasDerivAt (ha.trans_le hx.1)).continuousAt
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hp : ContinuousAt (fun x : ℝ => (N : ℝ) ^ (x - 1)) x := by fun_prop
  exact ((hp.mul continuousAt_const).mul hc).continuousWithinAt

theorem kernel_integrable {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (kernel N) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact continuousOn_kernel hN ha

theorem kernel_nonneg {N : ℕ} (hN : 1 ≤ N) {alpha : ℝ} (ha : 0 < alpha) :
    0 ≤ kernel N alpha := by
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.log_nonneg (by exact_mod_cast hN))) (coefficient_nonneg ha)

theorem weight_hasDerivAt {N : ℕ} (hN : 0 < N) {alpha : ℝ} (ha : 0 < alpha) :
    HasDerivAt (weight N)
      (coefficientSlope alpha * (N : ℝ) ^ (alpha - 1) + kernel N alpha) alpha := by
  have h := (coefficient_hasDerivAt ha).mul
    (((hasDerivAt_id alpha).sub_const 1).const_rpow (Nat.cast_pos.mpr hN))
  apply h.congr_deriv
  dsimp [kernel, sourceL]
  ring

theorem weight_le_initial_add_integral {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    weight N b ≤ weight N a + ∫ alpha in a..b, kernel N alpha := by
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab
    (g := weight N)
    (g' := fun x => coefficientSlope x * (N : ℝ) ^ (x - 1) + kernel N x)
    (fun x hx => (weight_hasDerivAt hN (ha.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => (weight_hasDerivAt hN (ha.trans hx.1)).hasDerivWithinAt)
    ((continuousOn_kernel hN ha).integrableOn_Icc)
    (fun x _ => add_le_of_nonpos_left
      (mul_nonpos_of_nonpos_of_nonneg (coefficientSlope_nonpos x)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  linarith

theorem integral_power_kernel {N : ℕ} (hN : 0 < N) (a b : ℝ) :
    (∫ alpha in a..b, (N : ℝ) ^ (alpha - 1) * sourceL N) =
      (N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    simpa only [sourceL, id_eq, mul_one, mul_comm, one_mul] using
      (((hasDerivAt_id x).sub_const 1).const_rpow (Nat.cast_pos.mpr hN))
  · have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
    have hc : Continuous (fun x : ℝ => (N : ℝ) ^ (x - 1) * sourceL N) := by fun_prop
    exact hc.intervalIntegrable _ _

theorem integral_kernel_le_endpoint_difference {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ alpha in a..b, kernel N alpha) ≤
      coefficient a * ((N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1)) := by
  rw [← integral_power_kernel hN, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab (kernel_integrable hN ha hab)
  · have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
    have hc : Continuous (fun x : ℝ => coefficient a *
        ((N : ℝ) ^ (x - 1) * sourceL N)) := by fun_prop
    exact hc.intervalIntegrable _ _
  · intro x hx
    dsimp [kernel]
    rw [mul_comm (coefficient a)]
    exact mul_le_mul_of_nonneg_left
      (coefficient_antitone ha (ha.trans_le hx.1) hx.1)
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.log_nonneg (by exact_mod_cast hN)))

end LiuWang.Proof.SourceRoute.LowSum
