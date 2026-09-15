import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral.Envelope
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral.ExponentialMoments

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral

def cellPrimitive (H u v m y : ℝ) : ℝ :=
  H / ((H - 4 * u) * (H - 4 * v)) *
    ((H - 4 * v) *
      (254231 * expPrimitive (phaseSlope H m) (phaseIntercept H m) 5 y +
        33643 * expPrimitive (phaseSlope H m) (phaseIntercept H m) 6 y) +
      4 * (254231 * (expPrimitive (phaseSlope H m) (phaseIntercept H m) 6 y -
          u * expPrimitive (phaseSlope H m) (phaseIntercept H m) 5 y) +
        33643 * (expPrimitive (phaseSlope H m) (phaseIntercept H m) 7 y -
          u * expPrimitive (phaseSlope H m) (phaseIntercept H m) 6 y)))

def cellValue (H u v m : ℝ) : ℝ :=
  H / ((H - 4 * u) * (H - 4 * v)) *
    ((H - 4 * v) *
      (254231 * expMoment 5 (phaseSlope H m) (phaseIntercept H m) u v +
        33643 * expMoment 6 (phaseSlope H m) (phaseIntercept H m) u v) +
      4 * (254231 * (expMoment 6 (phaseSlope H m) (phaseIntercept H m) u v -
          u * expMoment 5 (phaseSlope H m) (phaseIntercept H m) u v) +
        33643 * (expMoment 7 (phaseSlope H m) (phaseIntercept H m) u v -
          u * expMoment 6 (phaseSlope H m) (phaseIntercept H m) u v)))

theorem cellPrimitive_hasDerivAt (H u v m y : ℝ) :
    HasDerivAt (cellPrimitive H u v m) (cellEnvelope H u v m y) y := by
  have h5 := expPrimitive_hasDerivAt 5 (phaseSlope H m) (phaseIntercept H m) y
  have h6 := expPrimitive_hasDerivAt 6 (phaseSlope H m) (phaseIntercept H m) y
  have h7 := expPrimitive_hasDerivAt 7 (phaseSlope H m) (phaseIntercept H m) y
  have hbase := ((h5.const_mul 254231).add (h6.const_mul 33643)).const_mul (H - 4 * v)
  have hshift := (((h6.sub (h5.const_mul u)).const_mul 254231).add
    ((h7.sub (h6.const_mul u)).const_mul 33643)).const_mul 4
  convert! ((hbase.add hshift).const_mul (H / ((H - 4 * u) * (H - 4 * v)))) using 1
  unfold cellEnvelope denominatorChord sourcePolynomial
  ring

theorem cellValue_eq_primitive (H u v m : ℝ) :
    cellValue H u v m = cellPrimitive H u v m v - cellPrimitive H u v m u := by
  unfold cellValue cellPrimitive expMoment
  ring

theorem integral_cellEnvelope (H u v m : ℝ) :
    (∫ y in u..v, cellEnvelope H u v m y) = cellValue H u v m := by
  rw [cellValue_eq_primitive]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => cellPrimitive_hasDerivAt H u v m y)
    ((cellEnvelope_continuous H u v m).intervalIntegrable u v)

theorem shifted_expMoment_nonnegative (n : ℕ) {s b u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    0 ≤ expMoment (n + 1) s b u v - u * expMoment n s b u v := by
  have hi (k : ℕ) : IntervalIntegrable (fun y : ℝ => y ^ k * Real.exp (s * y + b))
      volume u v := (by fun_prop : Continuous
        (fun y : ℝ => y ^ k * Real.exp (s * y + b))).intervalIntegrable u v
  rw [← integral_power_exp, ← integral_power_exp, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hi (n + 1)) ((hi n).const_mul u)]
  apply intervalIntegral.integral_nonneg huv
  intro y hy
  have hy0 : 0 ≤ y := hu.trans hy.1
  have hp := mul_nonneg (mul_nonneg (pow_nonneg hy0 n) (sub_nonneg.mpr hy.1))
    (Real.exp_pos (s * y + b)).le
  rw [pow_succ]
  nlinarith only [hp]

theorem cellValue_nonnegative {H u v m : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (hH : 4 * v < H) :
    0 ≤ cellValue H u v m := by
  have hHu : 0 < H - 4 * u := by linarith
  have hHv : 0 < H - 4 * v := by linarith
  have hHp : 0 < H := by linarith
  have h5 := expMoment_nonnegative 5 (s := phaseSlope H m) (b := phaseIntercept H m) hu.le huv
  have h6 := expMoment_nonnegative 6 (s := phaseSlope H m) (b := phaseIntercept H m) hu.le huv
  have hs5 := shifted_expMoment_nonnegative 5 (s := phaseSlope H m) (b := phaseIntercept H m) hu.le huv
  have hs6 := shifted_expMoment_nonnegative 6 (s := phaseSlope H m) (b := phaseIntercept H m) hu.le huv
  unfold cellValue
  positivity

theorem density_integral_le_cellValue {H u v m : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (hm : m ∈ Set.Icc u v) (hH : 4 * v < H) :
    (∫ y in u..v, densityKernel H y) ≤ cellValue H u v m := by
  rw [← integral_cellEnvelope]
  exact intervalIntegral.integral_mono_on huv
    ((densityKernel_continuousOn hu hH).intervalIntegrable_of_Icc huv)
    ((cellEnvelope_continuous H u v m).intervalIntegrable u v)
    (fun y hy => densityKernel_le_cellEnvelope hu hy hm hH)

theorem cellValue_degenerate (H u m : ℝ) : cellValue H u u m = 0 := by
  rw [← integral_cellEnvelope, intervalIntegral.integral_same]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral
