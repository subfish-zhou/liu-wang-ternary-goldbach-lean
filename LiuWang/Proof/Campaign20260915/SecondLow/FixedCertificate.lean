import LiuWang.Proof.Campaign20260915.SecondLow.FixedEnvelope

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.Campaign20260915.SecondLow

open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def affineAmplitude (A B s y : ℝ) : ℝ :=
  A * Fixed032281.primitiveCoefficient s 1 y + B * Fixed032281.primitiveCoefficient s 0 y

theorem affineExpValue_factor {A B a c m u v : ℝ} (hs : tangentSlope a c m ≠ 0) :
    affineExpValue A B a c m u v =
      affineAmplitude A B (tangentSlope a c m) v *
        Real.exp (tangentSlope a c m * v + tangentIntercept a m) -
      affineAmplitude A B (tangentSlope a c m) u *
        Real.exp (tangentSlope a c m * u + tangentIntercept a m) := by
  unfold affineExpValue FixedIntegral.expMoment affineAmplitude
  rw [Fixed032281.primitive_factor hs, Fixed032281.primitive_factor hs,
    Fixed032281.primitive_factor hs, Fixed032281.primitive_factor hs]
  ring

def affineExpUpper (A B a c m u v : ℝ) : ℝ :=
  let s := tangentSlope a c m
  let b := tangentIntercept a m
  let Av := affineAmplitude A B s v
  let Au := affineAmplitude A B s u
  Av * (if 0 ≤ Av then Fixed032281.expUpper (s * v + b) else Fixed032281.expLower (s * v + b)) -
    Au * (if 0 ≤ Au then Fixed032281.expLower (s * u + b) else Fixed032281.expUpper (s * u + b))

theorem affineExpValue_le_upper {A B a c m u v : ℝ}
    (hs : tangentSlope a c m ≠ 0)
    (hu : |tangentSlope a c m * u + tangentIntercept a m| ≤ 256)
    (hv : |tangentSlope a c m * v + tangentIntercept a m| ≤ 256) :
    affineExpValue A B a c m u v ≤ affineExpUpper A B a c m u v := by
  rw [affineExpValue_factor hs]
  exact sub_le_sub (Fixed032281.mul_exp_upper hv) (Fixed032281.mul_exp_lower hu)

theorem fixed_tangent_domain {c m z : ℝ}
    (hc : c ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) (hm : m ∈ Set.Icc 25 37)
    (hz : z ∈ Set.Icc 25 37) :
    tangentSlope fixedParameter c m ≠ 0 ∧
      |tangentSlope fixedParameter c m * z + tangentIntercept fixedParameter m| ≤ 256 := by
  have hm0 : 0 < m := by linarith [hm.1]
  have hm2lo : (625 : ℝ) ≤ m ^ (2 : ℕ) := by nlinarith [hm.1, sq_nonneg (m - 25)]
  have hm2hi : m ^ (2 : ℕ) ≤ (1369 : ℝ) := by nlinarith [hm.2]
  have hdiv0 : (1 : ℝ) ≤ fixedParameter / m ^ (2 : ℕ) :=
    (le_div_iff₀ (by positivity)).mpr (by norm_num [fixedParameter]; nlinarith)
  have hdiv3 : fixedParameter / m ^ (2 : ℕ) ≤ (3 : ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by norm_num [fixedParameter]; nlinarith)
  have hb0 : tangentIntercept fixedParameter m ≤ 0 := by
    unfold tangentIntercept fixedParameter
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hm0.le
  have hb120 : -(120 : ℝ) ≤ tangentIntercept fixedParameter m := by
    unfold tangentIntercept fixedParameter
    apply (le_div_iff₀ hm0).mpr
    linarith [hm.1]
  have hs0 : 0 < tangentSlope fixedParameter c m := by
    unfold tangentSlope
    linarith [hc.1]
  have hs4 : tangentSlope fixedParameter c m ≤ 4 := by
    unfold tangentSlope
    linarith [hc.2]
  have hp0 := mul_nonneg hs0.le (by linarith [hz.1] : 0 ≤ z)
  have hp4 := mul_le_mul_of_nonneg_right hs4 (by linarith [hz.1] : 0 ≤ z)
  exact ⟨hs0.ne', abs_le.mpr ⟨by linarith, by linarith [hz.2]⟩⟩

def lowFixedCellUpper (i : ℕ) : ℝ :=
  Fixed032281.roundUp 20
    (affineExpUpper fixedA₁ fixedB₁ fixedParameter (1 / 2) (lowFixedMidpoint i)
      (lowFixedPoint i) (lowFixedPoint (i + 1)) +
    affineExpUpper fixedA₂ fixedB₂ fixedParameter (-1 / 2) (lowFixedMidpoint i)
      (lowFixedPoint i) (lowFixedPoint (i + 1)))

theorem lowFixedCellValue_le_upper {i : ℕ} (hi : i < 16) :
    lowFixedCellValue i ≤ lowFixedCellUpper i := by
  have hu : lowFixedPoint i ∈ Set.Icc 25 37 := by
    refine ⟨lowFixedPoint_ge i, ?_⟩
    exact (lowFixedPoint_monotone hi.le).trans (by norm_num [lowFixedPoint])
  have hv : lowFixedPoint (i + 1) ∈ Set.Icc 25 37 := by
    refine ⟨lowFixedPoint_ge (i + 1), ?_⟩
    exact (lowFixedPoint_monotone (show i + 1 ≤ 16 from hi)).trans (by norm_num [lowFixedPoint])
  have hm : lowFixedMidpoint i ∈ Set.Icc 25 37 := by
    unfold lowFixedMidpoint
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have h₁u := fixed_tangent_domain (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (-1 / 2) (1 / 2)) hm hu
  have h₁v := fixed_tangent_domain (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (-1 / 2) (1 / 2)) hm hv
  have h₂u := fixed_tangent_domain (by norm_num : (-1 / 2 : ℝ) ∈ Set.Icc (-1 / 2) (1 / 2)) hm hu
  have h₂v := fixed_tangent_domain (by norm_num : (-1 / 2 : ℝ) ∈ Set.Icc (-1 / 2) (1 / 2)) hm hv
  exact (add_le_add (affineExpValue_le_upper h₁u.1 h₁u.2 h₁v.2)
    (affineExpValue_le_upper h₂u.1 h₂u.2 h₂v.2)).trans (Fixed032281.le_roundUp _ _)

theorem originalLowScalar_fixed_rational_reduction :
    originalLowScalar 3100 ≤ ∑ i ∈ Finset.range 16, lowFixedCellUpper i :=
  originalLowScalar_fixed_partition.trans
    (Finset.sum_le_sum (fun _ hi => lowFixedCellValue_le_upper (Finset.mem_range.mp hi)))

end LiuWang.Proof.Campaign20260915.SecondLow
