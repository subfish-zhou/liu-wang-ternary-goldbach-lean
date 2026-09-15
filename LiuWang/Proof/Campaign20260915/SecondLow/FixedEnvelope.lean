import LiuWang.Proof.Campaign20260915.SecondLow.Tangent

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.Campaign20260915.SecondLow

open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def fixedParameter : ℝ := 0.478 * 3093.092244719
def fixedA₁ : ℝ := 3100 / 3.141592
def fixedB₁ : ℝ := 3100 * (24.117472185 / 3.141592 - 0.874)
def fixedA₂ : ℝ := 6.8423 * (3100 : ℝ) ^ (4 : ℕ)
def fixedB₂ : ℝ := (3100 : ℝ) ^ (4 : ℕ) * (6.8423 * 24.117472185 + 15)

def fixedKernel (z : ℝ) : ℝ :=
  (fixedA₁ * z + fixedB₁) * Real.exp (z / 2 - fixedParameter / z) +
    (fixedA₂ * z + fixedB₂) * Real.exp (-z / 2 - fixedParameter / z)

theorem fixedKernel_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ fixedKernel z := by
  have ha₁ : 0 ≤ fixedA₁ := by norm_num [fixedA₁]
  have hb₁ : 0 ≤ fixedB₁ := by norm_num [fixedB₁]
  have ha₂ : 0 ≤ fixedA₂ := by norm_num [fixedA₂]
  have hb₂ : 0 ≤ fixedB₂ := by norm_num [fixedB₂]
  unfold fixedKernel
  positivity

theorem fixedKernel_continuousOn {u v : ℝ} (hu : 0 < u) :
    ContinuousOn fixedKernel (Set.Icc u v) := by
  have hz : ∀ z ∈ Set.Icc u v, z ≠ 0 := fun z hz => (hu.trans_le hz.1).ne'
  have he : ContinuousOn (fun z : ℝ => fixedParameter / z) (Set.Icc u v) :=
    continuousOn_const.div continuousOn_id hz
  exact ((((continuousOn_const.mul continuousOn_id).add continuousOn_const).mul
    (Real.continuous_exp.comp_continuousOn ((continuousOn_id.div_const 2).sub he)))).add
    (((continuousOn_const.mul continuousOn_id).add continuousOn_const).mul
      (Real.continuous_exp.comp_continuousOn ((continuousOn_id.neg.div_const 2).sub he)))

theorem lowLogKernel_fixed_le {z : ℝ} (hz : 25 ≤ z) :
    lowLogKernel 3100 z ≤ fixedKernel z := by
  have hz0 : 0 < z := by linarith
  have hlog : 3 * Real.log (3100 : ℝ) ≤ 24.117472185 := by
    linarith [Fixed032281.log_3100_interval.2]
  have hratio : (z + 3 * Real.log (3100 : ℝ)) / Real.pi ≤
      (z + 24.117472185) / 3.141592 := by
    calc
      _ ≤ (z + 24.117472185) / Real.pi :=
        div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (by norm_num) Real.pi_gt_d6.le
  have ha₁ : 3100 * ((z + 3 * Real.log (3100 : ℝ)) / Real.pi - 0.874) ≤
      fixedA₁ * z + fixedB₁ := by
    calc
      _ ≤ 3100 * ((z + 24.117472185) / 3.141592 - 0.874) :=
        mul_le_mul_of_nonneg_left (sub_le_sub hratio le_rfl) (by norm_num)
      _ = _ := by unfold fixedA₁ fixedB₁; ring
  have ha₂ : 3100 * (3100 : ℝ) ^ (3 : ℕ) *
      (6.8423 * (z + 3 * Real.log (3100 : ℝ)) + 15) ≤ fixedA₂ * z + fixedB₂ := by
    unfold fixedA₂ fixedB₂
    nlinarith only [hlog]
  have hphase : fixedParameter / z ≤ 0.478 * (3100 + Real.log 0.001) / z :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left Fixed032281.window_H_lower (by norm_num)) hz0.le
  have he₁ : Real.exp (z / 2 - 0.478 * (3100 + Real.log 0.001) / z) ≤
      Real.exp (z / 2 - fixedParameter / z) :=
    Real.exp_le_exp.mpr (by linarith)
  have he₂ : Real.exp (-z / 2 - 0.478 * (3100 + Real.log 0.001) / z) ≤
      Real.exp (-z / 2 - fixedParameter / z) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold lowLogKernel fixedKernel
  exact add_le_add
    (mul_le_mul ha₁ he₁ (Real.exp_pos _).le (by
      norm_num [fixedA₁, fixedB₁]; positivity))
    (mul_le_mul ha₂ he₂ (Real.exp_pos _).le (by
      norm_num [fixedA₂, fixedB₂]; positivity))

theorem originalLowScalar_fixed_enclosure :
    originalLowScalar 3100 ≤ ∫ z in (25 : ℝ)..36.510750, fixedKernel z := by
  have hd := low_base_bounds
  have hab : lowerLog 3100 ≤ lowUpperLog 3100 := by linarith [hd.2.2]
  have ha : 25 ≤ lowerLog 3100 := by linarith [Fixed032281.lower_endpoint]
  rw [originalLowScalar_log (by norm_num)]
  apply le_trans (intervalIntegral.integral_mono_on hab
    ((lowLogKernel_continuousOn 3100 (by linarith : 0 < lowerLog 3100)).intervalIntegrable_of_Icc hab)
    ((fixedKernel_continuousOn (by linarith : 0 < lowerLog 3100)).intervalIntegrable_of_Icc hab)
    (fun z hz => lowLogKernel_fixed_le (ha.trans hz.1))) ?_
  exact intervalIntegral.integral_mono_interval ha hab hd.2.1
    (by
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro z hz
      exact fixedKernel_nonneg (by linarith [hz.1]))
    ((fixedKernel_continuousOn (by norm_num : (0 : ℝ) < 25)).intervalIntegrable_of_Icc
      (by norm_num : (25 : ℝ) ≤ 36.510750))

def lowFixedPoint (i : ℕ) : ℝ := 25 + (36.510750 - 25) * i / 16
def lowFixedMidpoint (i : ℕ) : ℝ := (lowFixedPoint i + lowFixedPoint (i + 1)) / 2

def lowFixedCellValue (i : ℕ) : ℝ :=
  affineExpValue fixedA₁ fixedB₁ fixedParameter (1 / 2) (lowFixedMidpoint i)
    (lowFixedPoint i) (lowFixedPoint (i + 1)) +
  affineExpValue fixedA₂ fixedB₂ fixedParameter (-1 / 2) (lowFixedMidpoint i)
    (lowFixedPoint i) (lowFixedPoint (i + 1))

theorem lowFixedPoint_monotone : Monotone lowFixedPoint := by
  intro i j hij
  have hh : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  unfold lowFixedPoint
  linarith

theorem lowFixedPoint_ge (i : ℕ) : 25 ≤ lowFixedPoint i := by
  have hh := Nat.cast_nonneg (α := ℝ) i
  unfold lowFixedPoint
  linarith

theorem fixedKernel_integral_le_cell (i : ℕ) :
    (∫ z in lowFixedPoint i..lowFixedPoint (i + 1), fixedKernel z) ≤ lowFixedCellValue i := by
  have hu : 0 < lowFixedPoint i := by linarith [lowFixedPoint_ge i]
  have huv := lowFixedPoint_monotone (Nat.le_succ i)
  have hm : 0 < lowFixedMidpoint i := by unfold lowFixedMidpoint; linarith
  have h₁ := affine_exp_integral_le (A := fixedA₁) (B := fixedB₁) (a := fixedParameter)
    (c := (1 / 2 : ℝ)) (by norm_num [fixedParameter]) hm hu huv (by
      intro z hz
      have hz0 : 0 ≤ z := (hu.trans_le hz.1).le
      norm_num [fixedA₁, fixedB₁]
      positivity)
  have h₂ := affine_exp_integral_le (A := fixedA₂) (B := fixedB₂) (a := fixedParameter)
    (c := (-1 / 2 : ℝ)) (by norm_num [fixedParameter]) hm hu huv (by
      intro z hz
      have hz0 : 0 ≤ z := (hu.trans_le hz.1).le
      norm_num [fixedA₂, fixedB₂]
      positivity)
  have hz : ∀ z ∈ Set.Icc (lowFixedPoint i) (lowFixedPoint (i + 1)), z ≠ 0 :=
    fun z hz => (hu.trans_le hz.1).ne'
  have he (c : ℝ) : ContinuousOn (fun z : ℝ => Real.exp (c * z - fixedParameter / z))
      (Set.Icc (lowFixedPoint i) (lowFixedPoint (i + 1))) :=
    Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul continuousOn_id).sub (continuousOn_const.div continuousOn_id hz))
  have hcont₁ : IntervalIntegrable
      (fun z : ℝ => (fixedA₁ * z + fixedB₁) * Real.exp ((1 / 2) * z - fixedParameter / z))
      volume (lowFixedPoint i) (lowFixedPoint (i + 1)) :=
    (((continuousOn_const.mul continuousOn_id).add continuousOn_const).mul
      (he (1 / 2))).intervalIntegrable_of_Icc huv
  have hcont₂ : IntervalIntegrable
      (fun z : ℝ => (fixedA₂ * z + fixedB₂) * Real.exp ((-1 / 2) * z - fixedParameter / z))
      volume (lowFixedPoint i) (lowFixedPoint (i + 1)) :=
    (((continuousOn_const.mul continuousOn_id).add continuousOn_const).mul
      (he (-1 / 2))).intervalIntegrable_of_Icc huv
  have hadd := add_le_add h₁ h₂
  rw [← intervalIntegral.integral_add hcont₁ hcont₂] at hadd
  apply le_trans (le_of_eq ?_) hadd
  apply intervalIntegral.integral_congr
  intro z _
  unfold fixedKernel
  ring_nf

theorem originalLowScalar_fixed_partition :
    originalLowScalar 3100 ≤ ∑ i ∈ Finset.range 16, lowFixedCellValue i := by
  apply originalLowScalar_fixed_enclosure.trans
  have hint (i : ℕ) (_hi : i < 16) :
      IntervalIntegrable fixedKernel volume (lowFixedPoint i) (lowFixedPoint (i + 1)) :=
    (fixedKernel_continuousOn (by linarith [lowFixedPoint_ge i] : 0 < lowFixedPoint i)).intervalIntegrable_of_Icc
      (lowFixedPoint_monotone (Nat.le_succ i))
  have he := intervalIntegral.sum_integral_adjacent_intervals hint
  have hp0 : lowFixedPoint 0 = 25 := by norm_num [lowFixedPoint]
  have hp16 : lowFixedPoint 16 = 36.510750 := by norm_num [lowFixedPoint]
  rw [hp0, hp16] at he
  rw [← he]
  exact Finset.sum_le_sum (fun i _ => fixedKernel_integral_le_cell i)

end LiuWang.Proof.Campaign20260915.SecondLow
