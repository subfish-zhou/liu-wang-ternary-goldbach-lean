import LiuWang.Proof.Campaign20260915.SecondLow.Uniform

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.Campaign20260915.SecondLow

open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def tangentSlope (a c m : ℝ) : ℝ := c + a / m ^ (2 : ℕ)
def tangentIntercept (a m : ℝ) : ℝ := -2 * a / m

theorem exp_le_affine_tangent {a c m z : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hz : 0 < z) :
    Real.exp (c * z - a / z) ≤
      Real.exp (tangentSlope a c m * z + tangentIntercept a m) := by
  apply (exp_linear_sub_div_le_tangent ha hz hm).trans_eq
  rw [← Real.exp_add]
  congr 1
  unfold tangentSlope tangentIntercept
  field_simp
  ring

def affineExpValue (A B a c m u v : ℝ) : ℝ :=
  A * FixedIntegral.expMoment 1 (tangentSlope a c m) (tangentIntercept a m) u v +
    B * FixedIntegral.expMoment 0 (tangentSlope a c m) (tangentIntercept a m) u v

theorem affine_tangent_integral (A B a c m u v : ℝ) :
    (∫ z in u..v, (A * z + B) *
      Real.exp (tangentSlope a c m * z + tangentIntercept a m)) =
        affineExpValue A B a c m u v := by
  unfold affineExpValue
  rw [← FixedIntegral.integral_power_exp, ← FixedIntegral.integral_power_exp,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  apply intervalIntegral.integral_congr
  intro z _
  simp only [pow_one, pow_zero, one_mul]
  ring

theorem affine_exp_integral_le {A B a c m u v : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hu : 0 < u) (huv : u ≤ v)
    (hamp : ∀ z ∈ Set.Icc u v, 0 ≤ A * z + B) :
    (∫ z in u..v, (A * z + B) * Real.exp (c * z - a / z)) ≤
      affineExpValue A B a c m u v := by
  have hz : ∀ z ∈ Set.Icc u v, z ≠ 0 := fun z hz => (hu.trans_le hz.1).ne'
  have hc : ContinuousOn (fun z : ℝ => (A * z + B) * Real.exp (c * z - a / z))
      (Set.Icc u v) :=
    ((continuousOn_const.mul continuousOn_id).add continuousOn_const).mul
      (Real.continuous_exp.comp_continuousOn
        ((continuousOn_const.mul continuousOn_id).sub (continuousOn_const.div continuousOn_id hz)))
  rw [← affine_tangent_integral]
  apply intervalIntegral.integral_mono_on huv (hc.intervalIntegrable_of_Icc huv)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro z hz
  exact mul_le_mul_of_nonneg_left (exp_le_affine_tangent ha hm (hu.trans_le hz.1)) (hamp z hz)

def lowTangentValue (L m₁ m₂ u v : ℝ) : ℝ :=
  affineExpValue (L / Real.pi) (L * (3 * Real.log L / Real.pi - 0.874))
    (0.478 * (L + Real.log 0.001)) (1 / 2) m₁ u v +
  affineExpValue (6.8423 * L ^ (4 : ℕ)) (L ^ (4 : ℕ) * (6.8423 * (3 * Real.log L) + 15))
    (0.478 * (L + Real.log 0.001)) (-1 / 2) m₂ u v

theorem low_integral_le_tangent {L m₁ m₂ u v : ℝ}
    (hL : 3100 ≤ L) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hu : 20 ≤ u) (huv : u ≤ v) :
    (∫ z in u..v, lowLogKernel L z) ≤ lowTangentValue L m₁ m₂ u v := by
  have hL0 : 0 < L := by linarith
  have hlog : 7 ≤ Real.log L :=
    SourceRoute.SecondArc.Continuation.log_3100_bounds.1.trans
      (Real.log_le_log (by norm_num) hL)
  have hlog0 : 0 ≤ Real.log L := by linarith
  have h₁ := affine_exp_integral_le (A := L / Real.pi)
    (B := L * (3 * Real.log L / Real.pi - 0.874)) (c := (1 / 2 : ℝ))
    (original_low_parameter_nonneg hL) hm₁ (by linarith : 0 < u) huv (by
      intro z hz
      have ha : 0.874 ≤ (z + 3 * Real.log L) / Real.pi :=
        (le_div_iff₀ Real.pi_pos).mpr (by linarith [hz.1, Real.pi_lt_d2])
      have hp := mul_nonneg hL0.le (sub_nonneg.mpr ha)
      have he : L / Real.pi * z + L * (3 * Real.log L / Real.pi - 0.874) =
          L * ((z + 3 * Real.log L) / Real.pi - 0.874) := by ring
      rwa [he])
  have h₂ := affine_exp_integral_le (A := 6.8423 * L ^ (4 : ℕ))
    (B := L ^ (4 : ℕ) * (6.8423 * (3 * Real.log L) + 15)) (c := (-1 / 2 : ℝ))
    (original_low_parameter_nonneg hL) hm₂ (by linarith : 0 < u) huv (by
      intro z hz
      have hz0 : 0 ≤ z := by linarith [hz.1]
      positivity)
  have hz : ∀ z ∈ Set.Icc u v, z ≠ 0 := fun z hz => ne_of_gt (by linarith [hz.1])
  have he (c : ℝ) : ContinuousOn
      (fun z : ℝ => Real.exp (c * z - 0.478 * (L + Real.log 0.001) / z))
      (Set.Icc u v) :=
    Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul continuousOn_id).sub (continuousOn_const.div continuousOn_id hz))
  have hcont₁ : IntervalIntegrable
      (fun z : ℝ => (L / Real.pi * z + L * (3 * Real.log L / Real.pi - 0.874)) *
        Real.exp ((1 / 2) * z - 0.478 * (L + Real.log 0.001) / z)) volume u v :=
    (((continuousOn_const.mul continuousOn_id).add continuousOn_const).mul
      (he (1 / 2))).intervalIntegrable_of_Icc huv
  have hcont₂ : IntervalIntegrable
      (fun z : ℝ => (6.8423 * L ^ (4 : ℕ) * z +
          L ^ (4 : ℕ) * (6.8423 * (3 * Real.log L) + 15)) *
        Real.exp ((-1 / 2) * z - 0.478 * (L + Real.log 0.001) / z)) volume u v :=
    (((continuousOn_const.mul continuousOn_id).add continuousOn_const).mul
      (he (-1 / 2))).intervalIntegrable_of_Icc huv
  have hadd := add_le_add h₁ h₂
  rw [← intervalIntegral.integral_add hcont₁ hcont₂] at hadd
  apply le_trans (le_of_eq ?_) hadd
  apply intervalIntegral.integral_congr
  intro z _
  unfold lowLogKernel
  ring_nf

theorem originalLowScalar_le_tangent {L : ℝ} (hL : 3100 ≤ L) :
    originalLowScalar L ≤ lowTangentValue L
      ((lowerLog L + lowUpperLog L) / 2) ((lowerLog L + lowUpperLog L) / 2)
      (lowerLog L) (lowUpperLog L) := by
  have hl : 20 ≤ lowerLog L := by
    rw [(source_log_scaling hL).1]
    have ht : 1 ≤ L / 3100 := by linarith
    linarith [low_base_bounds.1, Real.log_nonneg ht]
  have hd := low_scalar_domain hL
  have hab : lowerLog L ≤ lowUpperLog L := Real.log_le_log hd.1 hd.2.1
  rw [originalLowScalar_log hL]
  exact low_integral_le_tangent hL (by linarith) (by linarith) hl hab

end LiuWang.Proof.Campaign20260915.SecondLow
