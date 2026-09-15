import LiuWang.Proof.Campaign20260915.SecondTerminal.LastScaling
import LiuWang.Proof.Campaign20260915.SecondLow.FixedCertificate

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def lastFixedA : ℝ := 3093.092244719 / 9.645908801
def lastFixedB : ℝ := 0.2067 * 3100
def lastFixedKernel (z : ℝ) : ℝ :=
  Real.exp (-z / 2 - lastFixedA / z) - Real.exp (-z / 2 - lastFixedB / z)

theorem lastFixedKernel_nonneg {z : ℝ} (hz : 0 < z) :
    0 ≤ lastFixedKernel z := by
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_right
    (by norm_num [lastFixedA, lastFixedB] : lastFixedA ≤ lastFixedB) hz.le
  linarith

theorem lastFixedKernel_continuousOn {u v : ℝ} (hu : 0 < u) :
    ContinuousOn lastFixedKernel (Set.Icc u v) := by
  have hz : ∀ z ∈ Set.Icc u v, z ≠ 0 := fun z hz => (hu.trans_le hz.1).ne'
  exact (Real.continuous_exp.comp_continuousOn
    ((continuousOn_id.neg.div_const 2).sub (continuousOn_const.div continuousOn_id hz))).sub
    (Real.continuous_exp.comp_continuousOn
      ((continuousOn_id.neg.div_const 2).sub (continuousOn_const.div continuousOn_id hz)))

theorem lastKernel_fixed_le {z : ℝ} (hz : 0 < z) :
    lastKernel ((3100 : ℝ) + Real.log 0.001) z ≤ lastFixedKernel z := by
  have hA : lastFixedA ≤ ((1 : ℝ) / 9.645908801) *
      ((3100 : ℝ) + Real.log 0.001) := by
    unfold lastFixedA
    linarith [Fixed032281.window_H_lower]
  have hlog : Real.log (0.001 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hB : 0.2067 * ((3100 : ℝ) + Real.log 0.001) ≤ lastFixedB := by
    unfold lastFixedB
    linarith
  rw [lastKernel_phase_form]
  unfold lastFixedKernel
  apply sub_le_sub
  · apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_right hA hz.le
    linarith
  · apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_right hB hz.le
    linarith

def lastFixedCoefficient : ℝ :=
  16 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100

theorem originalLastScalar_fixed_enclosure :
    originalLastScalar 3100 ≤
      lastFixedCoefficient * ∫ z in (25.329413 : ℝ)..59.721417, lastFixedKernel z := by
  have hd := original_endpoints (L := (3100 : ℝ)) le_rfl
  have hk := intervalIntegral.integral_mono_on hd.2
    ((lastKernel_continuousOn hd.1).intervalIntegrable_of_Icc (μ := volume) hd.2)
    ((lastFixedKernel_continuousOn hd.1).intervalIntegrable_of_Icc hd.2)
    (fun z hz => lastKernel_fixed_le (hd.1.trans_le hz.1))
  have hi := intervalIntegral.integral_mono_interval (μ := volume) Fixed032281.lower_endpoint hd.2
    Fixed032281.upper_endpoint
    (by
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro z hz
      exact lastFixedKernel_nonneg (by linarith [hz.1]))
    ((lastFixedKernel_continuousOn (by norm_num : (0 : ℝ) < 25.329413)).intervalIntegrable_of_Icc
      (by norm_num : (25.329413 : ℝ) ≤ 59.721417))
  have hnonneg : 0 ≤ ∫ z in lowerLog 3100..upperLog 3100,
      lastKernel ((3100 : ℝ) + Real.log 0.001) z :=
    intervalIntegral.integral_nonneg hd.2 (fun z hz =>
      lastKernel_nonneg (by linarith [Fixed032281.window_H_lower]) (hd.1.trans_le hz.1))
  have hcoef : 16 * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100 ≤ lastFixedCoefficient := by
    unfold lastFixedCoefficient
    linarith [Fixed032281.sourceNu_fixed_upper]
  exact mul_le_mul hcoef (hk.trans hi) hnonneg (by norm_num [lastFixedCoefficient])

def lastFixedPoint (i : ℕ) : ℝ := 25.329413 + (59.721417 - 25.329413) * i / 32
def lastFixedMidpoint (i : ℕ) : ℝ := (lastFixedPoint i + lastFixedPoint (i + 1)) / 2

def lastFixedCellValue (i : ℕ) : ℝ :=
  SecondLow.affineExpValue 0 1 lastFixedA (-1 / 2) (lastFixedMidpoint i)
    (lastFixedPoint i) (lastFixedPoint (i + 1)) -
  (lastFixedPoint (i + 1) - lastFixedPoint i) *
    Real.exp (-lastFixedPoint (i + 1) / 2 - lastFixedB / lastFixedPoint i)

theorem lastFixedPoint_monotone : Monotone lastFixedPoint := by
  intro i j hij
  have h := Nat.cast_le (α := ℝ).mpr hij
  unfold lastFixedPoint
  linarith

theorem lastFixedPoint_ge (i : ℕ) : 25.329413 ≤ lastFixedPoint i := by
  have h := Nat.cast_nonneg (α := ℝ) i
  unfold lastFixedPoint
  linarith

theorem lastFixedKernel_integral_le_cell (i : ℕ) :
    (∫ z in lastFixedPoint i..lastFixedPoint (i + 1), lastFixedKernel z) ≤
      lastFixedCellValue i := by
  have hu : 0 < lastFixedPoint i := by linarith [lastFixedPoint_ge i]
  have huv := lastFixedPoint_monotone (Nat.le_succ i)
  have hm : 0 < lastFixedMidpoint i := by unfold lastFixedMidpoint; linarith
  have hz : ∀ z ∈ Set.Icc (lastFixedPoint i) (lastFixedPoint (i + 1)), z ≠ 0 :=
    fun z hz => (hu.trans_le hz.1).ne'
  have hc (A : ℝ) : ContinuousOn (fun z : ℝ => Real.exp (-z / 2 - A / z))
      (Set.Icc (lastFixedPoint i) (lastFixedPoint (i + 1))) :=
    Real.continuous_exp.comp_continuousOn
      ((continuousOn_id.neg.div_const 2).sub (continuousOn_const.div continuousOn_id hz))
  have hfirst := SecondLow.affine_exp_integral_le (A := 0) (B := 1)
    (a := lastFixedA) (c := (-1 / 2 : ℝ))
    (by norm_num [lastFixedA]) hm hu huv (by intros; norm_num)
  have hlinear (z : ℝ) : (-1 / 2 : ℝ) * z = -z / 2 := by ring
  simp only [zero_mul, zero_add, one_mul, hlinear] at hfirst
  have hsecond := intervalIntegral.integral_mono_on (μ := volume) huv
    (intervalIntegrable_const (c :=
      Real.exp (-lastFixedPoint (i + 1) / 2 - lastFixedB / lastFixedPoint i)))
    ((hc lastFixedB).intervalIntegrable_of_Icc huv) (fun z hz => by
      apply Real.exp_le_exp.mpr
      have h := div_le_div_of_nonneg_left
        (by norm_num [lastFixedB] : 0 ≤ lastFixedB) hu hz.1
      linarith [hz.2])
  rw [intervalIntegral.integral_const, smul_eq_mul] at hsecond
  have hadd := sub_le_sub hfirst hsecond
  rw [← intervalIntegral.integral_sub ((hc lastFixedA).intervalIntegrable_of_Icc huv)
    ((hc lastFixedB).intervalIntegrable_of_Icc huv)] at hadd
  exact hadd

theorem originalLastScalar_fixed_partition :
    originalLastScalar 3100 ≤ lastFixedCoefficient *
      ∑ i ∈ Finset.range 32, lastFixedCellValue i := by
  have hint (i : ℕ) (_ : i < 32) :
      IntervalIntegrable lastFixedKernel volume (lastFixedPoint i) (lastFixedPoint (i + 1)) :=
    (lastFixedKernel_continuousOn
      (by linarith [lastFixedPoint_ge i] : 0 < lastFixedPoint i)).intervalIntegrable_of_Icc
      (lastFixedPoint_monotone (Nat.le_succ i))
  have hi := intervalIntegral.sum_integral_adjacent_intervals hint
  have hbound := Finset.sum_le_sum
    (fun (i : ℕ) (_ : i ∈ Finset.range 32) => lastFixedKernel_integral_le_cell i)
  rw [hi] at hbound
  rw [show lastFixedPoint 0 = (25.329413 : ℝ) by norm_num [lastFixedPoint],
    show lastFixedPoint 32 = (59.721417 : ℝ) by norm_num [lastFixedPoint]] at hbound
  exact originalLastScalar_fixed_enclosure.trans
    (mul_le_mul_of_nonneg_left hbound (by norm_num [lastFixedCoefficient]))

#print axioms originalLastScalar_fixed_partition

end LiuWang.Proof.Campaign20260915.SecondTerminal
