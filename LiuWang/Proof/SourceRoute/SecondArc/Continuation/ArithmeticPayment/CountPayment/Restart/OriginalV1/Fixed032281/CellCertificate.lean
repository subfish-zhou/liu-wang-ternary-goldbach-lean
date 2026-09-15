import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.DirectedExp

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

open FixedIntegral

def primitiveCoefficient (s : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1 / s
  | n + 1, y => (y ^ (n + 1) - (n + 1) * primitiveCoefficient s n y) / s

theorem primitive_factor {s : ℝ} (hs : s ≠ 0) (b y : ℝ) (n : ℕ) :
    expPrimitive s b n y = primitiveCoefficient s n y * Real.exp (s * y + b) := by
  induction n with
  | zero => simp [expPrimitive, primitiveCoefficient, hs, div_eq_mul_inv, mul_comm]
  | succ n ih =>
    simp only [expPrimitive, hs, if_false, primitiveCoefficient, ih]
    ring

def primitiveAmplitude (H u v m y : ℝ) : ℝ :=
  H / ((H - 4 * u) * (H - 4 * v)) *
    ((H - 4 * v) *
      (254231 * primitiveCoefficient (phaseSlope H m) 5 y +
        33643 * primitiveCoefficient (phaseSlope H m) 6 y) +
      4 * (254231 * (primitiveCoefficient (phaseSlope H m) 6 y -
          u * primitiveCoefficient (phaseSlope H m) 5 y) +
        33643 * (primitiveCoefficient (phaseSlope H m) 7 y -
          u * primitiveCoefficient (phaseSlope H m) 6 y)))

def zeroAmplitude (H u v : ℝ) : ℝ :=
  H / ((H - 4 * u) * (H - 4 * v)) *
    ((H - 4 * v) * (254231 * ((v ^ (6 : ℕ) - u ^ (6 : ℕ)) / 6) +
      33643 * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7)) +
      4 * (254231 * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7 -
        u * ((v ^ (6 : ℕ) - u ^ (6 : ℕ)) / 6)) +
        33643 * ((v ^ (8 : ℕ) - u ^ (8 : ℕ)) / 8 -
          u * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7))))

def cellUpper (H u v m : ℝ) : ℝ :=
  if phaseSlope H m = 0 then
    zeroAmplitude H u v *
      (if 0 ≤ zeroAmplitude H u v then expUpper (phaseIntercept H m)
        else expLower (phaseIntercept H m))
  else
    primitiveAmplitude H u v m v *
      (if 0 ≤ primitiveAmplitude H u v m v then
        expUpper (phaseSlope H m * v + phaseIntercept H m)
      else expLower (phaseSlope H m * v + phaseIntercept H m)) -
    primitiveAmplitude H u v m u *
      (if 0 ≤ primitiveAmplitude H u v m u then
        expLower (phaseSlope H m * u + phaseIntercept H m)
      else expUpper (phaseSlope H m * u + phaseIntercept H m))

theorem cellValue_le_cellUpper {H u v m : ℝ}
    (hu : |phaseSlope H m * u + phaseIntercept H m| ≤ 256)
    (hv : |phaseSlope H m * v + phaseIntercept H m| ≤ 256)
    (hb : |phaseIntercept H m| ≤ 256) :
    cellValue H u v m ≤ cellUpper H u v m := by
  by_cases hs : phaseSlope H m = 0
  · rw [cellUpper, if_pos hs, cellValue_zero_slope hs]
    convert mul_exp_upper (a := zeroAmplitude H u v) hb using 1
    unfold zeroAmplitude
    ring
  · have he (y : ℝ) : cellPrimitive H u v m y =
        primitiveAmplitude H u v m y * Real.exp (phaseSlope H m * y + phaseIntercept H m) := by
      unfold cellPrimitive primitiveAmplitude
      rw [primitive_factor hs, primitive_factor hs, primitive_factor hs]
      ring
    rw [cellUpper, if_neg hs, cellValue_eq_primitive, he, he]
    exact sub_le_sub (mul_exp_upper hv) (mul_exp_lower hu)

theorem phase_certificate_domain {m y : ℝ} (hm : m ∈ Set.Icc 25 60)
    (hy : y ∈ Set.Icc 25 60) :
    |phaseSlope 3093.092244719 m * y + phaseIntercept 3093.092244719 m| ≤ 256 ∧
      |phaseIntercept 3093.092244719 m| ≤ 256 := by
  have hm0 : 0 < m := by linarith [hm.1]
  have hm2 : (625 : ℝ) ≤ m ^ (2 : ℕ) := by nlinarith [hm.1, sq_nonneg (m - 25)]
  have hdiv : 0 ≤ 0.478 * 3093.092244719 / m ^ (2 : ℕ) := by positivity
  have hdiv' : 0.478 * 3093.092244719 / m ^ (2 : ℕ) ≤ (3 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : -(120 : ℝ) ≤ -0.956 * 3093.092244719 / m := by
    apply (le_div_iff₀ hm0).mpr
    linarith [hm.1]
  have hb' : -0.956 * 3093.092244719 / m ≤ (0 : ℝ) := by
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hm0.le
  have hlo := mul_nonneg hdiv (by linarith [hy.1] : 0 ≤ y)
  have hhi := mul_nonneg (sub_nonneg.mpr hdiv') (by linarith [hy.1] : 0 ≤ y)
  unfold phaseSlope phaseIntercept
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [hy.1, hy.2]

def fixedCellUpper (i : ℕ) : ℝ :=
  cellUpper 3093.092244719 (fixedPoint i) (fixedPoint (i + 1)) (fixedMidpoint i)

theorem fixedCell_bound {i : ℕ} (hi : i < 256) :
    cellValue 3093.092244719 (fixedPoint i) (fixedPoint (i + 1)) (fixedMidpoint i) ≤
      fixedCellUpper i := by
  have hu : fixedPoint i ∈ Set.Icc 25 60 := by
    have h := Nat.cast_le (α := ℝ).mpr hi.le
    norm_num only [Nat.cast_ofNat] at h
    have h0 := Nat.cast_nonneg (α := ℝ) i
    unfold fixedPoint
    constructor <;> linarith
  have hv : fixedPoint (i + 1) ∈ Set.Icc 25 60 := by
    have h := Nat.cast_le (α := ℝ).mpr (show i + 1 ≤ 256 from hi)
    norm_num only [Nat.cast_ofNat] at h
    have h0 := Nat.cast_nonneg (α := ℝ) (i + 1)
    unfold fixedPoint
    constructor <;> linarith
  have hm : fixedMidpoint i ∈ Set.Icc 25 60 := by
    unfold fixedMidpoint
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  exact cellValue_le_cellUpper (phase_certificate_domain hm hu).1
    (phase_certificate_domain hm hv).1 (phase_certificate_domain hm hu).2

theorem fixed_rational_reduction :
    originalDensityScalar 3100 ≤
      (8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100) *
        ∑ i ∈ Finset.range 256, fixedCellUpper i := by
  apply fixed_partition_bound.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun i hi => fixedCell_bound (Finset.mem_range.mp hi))

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
