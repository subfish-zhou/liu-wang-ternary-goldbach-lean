import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.LogScalar
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.ExpTangent

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.SecondLow

open SourceRoute.SecondArc.Continuation
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem lowUpperLog_eq {L : ℝ} (hL : 1 < L) :
    lowUpperLog L = Real.log 10000 + 3 * Real.log L +
      Real.log (Real.log (L ^ (3 : ℕ))) := by
  unfold lowUpperLog scaledGate
  have hL0 : 0 < L := by linarith
  rw [Real.log_mul (by positivity) (by
    rw [Real.log_pow]
    exact mul_ne_zero (by norm_num) (Real.log_pos hL).ne')]
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  norm_num

theorem low_base_bounds :
    20 ≤ lowerLog 3100 ∧ lowUpperLog 3100 ≤ 36.510750 ∧
      1 ≤ lowUpperLog 3100 - lowerLog 3100 := by
  have hlog := Fixed032281.log_3100_interval
  have hloglog := Fixed032281.loglog_interval
  have hten : Real.log (10000 : ℝ) = 4 * (Real.log 2 + Real.log 5) := by
    rw [show (10000 : ℝ) = (2 * 5) ^ (4 : ℕ) by norm_num,
      Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlo : lowerLog 3100 ≤ 3 + 3 * Real.log (3100 : ℝ) := by
    unfold lowerLog
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3.36)
    norm_num only [Nat.cast_ofNat]
    linarith
  rw [lowUpperLog_eq (by norm_num), hten]
  exact ⟨base_log_domain.1, by
    linarith [hlog.2, hloglog.2, Real.log_two_lt_d9, Real.log_five_lt_d9], by
    have hnum : (4 : ℝ) ≤ 4 * (Real.log 2 + Real.log 5) := by
      linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have hll0 := (show (0 : ℝ) ≤ 3.182936 by norm_num).trans hloglog.1
    linarith only [hnum, hll0, hlo]⟩

def loglogShift (L : ℝ) : ℝ :=
  Real.log (Real.log (L ^ (3 : ℕ)) / Real.log ((3100 : ℝ) ^ (3 : ℕ)))

theorem loglogShift_bounds {L : ℝ} (hL : 3100 ≤ L) :
    0 ≤ loglogShift L ∧ loglogShift L ≤ Real.log (L / 3100) := by
  have hL0 : 0 < L := by linarith
  have ht : 1 ≤ L / 3100 := by linarith
  have hb : 3 ≤ Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_3100_bounds.1]
  have hm : Real.log ((3100 : ℝ) ^ (3 : ℕ)) ≤ Real.log (L ^ (3 : ℕ)) :=
    Real.log_le_log (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 3)
  have he : Real.log (L ^ (3 : ℕ)) =
      Real.log ((3100 : ℝ) ^ (3 : ℕ)) + 3 * Real.log (L / 3100) := by
    rw [Real.log_div hL0.ne' (by norm_num)]
    simp only [Real.log_pow, Nat.cast_ofNat]
    ring
  have hscale : Real.log (L ^ (3 : ℕ)) ≤
      (L / 3100) * Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    rw [he]
    nlinarith [Real.log_le_sub_one_of_pos (by positivity : 0 < L / 3100),
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hb)]
  have hr : 1 ≤ Real.log (L ^ (3 : ℕ)) / Real.log ((3100 : ℝ) ^ (3 : ℕ)) :=
    (le_div_iff₀ (by linarith)).mpr (by simpa using hm)
  refine ⟨Real.log_nonneg hr, ?_⟩
  apply Real.log_le_log (by linarith : 0 <
    Real.log (L ^ (3 : ℕ)) / Real.log ((3100 : ℝ) ^ (3 : ℕ)))
  exact (div_le_iff₀ (by linarith)).mpr hscale

theorem low_upper_scaling {L : ℝ} (hL : 3100 ≤ L) :
    lowUpperLog L = lowUpperLog 3100 + 3 * Real.log (L / 3100) +
      loglogShift L := by
  have hL0 : 0 < L := by linarith
  have hb : 0 < Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    rw [Real.log_pow]
    have hh := log_3100_bounds.1
    positivity
  have hlog : 0 < Real.log (L ^ (3 : ℕ)) :=
    hb.trans_le (Real.log_le_log (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 3))
  rw [lowUpperLog_eq (by linarith : 1 < L), lowUpperLog_eq (by norm_num)]
  unfold loglogShift
  rw [Real.log_div hlog.ne' hb.ne', Real.log_div hL0.ne' (by norm_num)]
  ring

def lowAffineSlope (L : ℝ) : ℝ :=
  1 + loglogShift L / (lowUpperLog 3100 - lowerLog 3100)

def lowAffineOffset (L : ℝ) : ℝ :=
  lowerLog L - lowAffineSlope L * lowerLog 3100

theorem low_affine_domain {L : ℝ} (hL : 3100 ≤ L) :
    1 ≤ lowAffineSlope L ∧ lowAffineSlope L ≤ L / 3100 ∧
      lowAffineSlope L * lowerLog 3100 + lowAffineOffset L = lowerLog L ∧
      lowAffineSlope L * lowUpperLog 3100 + lowAffineOffset L = lowUpperLog L := by
  have hd := low_base_bounds
  have hw : 0 < lowUpperLog 3100 - lowerLog 3100 := by linarith [hd.2.2]
  have hs := loglogShift_bounds hL
  have hs0 := hs.1
  have ht : 1 ≤ L / 3100 := by linarith
  have hratio : loglogShift L / (lowUpperLog 3100 - lowerLog 3100) ≤
      loglogShift L := (div_le_iff₀ hw).mpr (by nlinarith [hd.2.2])
  refine ⟨by unfold lowAffineSlope; exact le_add_of_nonneg_right (by positivity), ?_, ?_, ?_⟩
  · unfold lowAffineSlope
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < L / 3100)]
  · unfold lowAffineOffset
    ring
  · unfold lowAffineOffset lowAffineSlope
    rw [(source_log_scaling hL).1, low_upper_scaling hL]
    field_simp
    ring

theorem low_affine_shift {L y : ℝ} (hL : 3100 ≤ L)
    (hy : y ∈ Set.Icc (lowerLog 3100) (lowUpperLog 3100)) :
    ∃ k : ℝ, 0 ≤ k ∧ k ≤ 7 ∧
      lowAffineSlope L * y + lowAffineOffset L =
        y + k * Real.log (L / 3100) := by
  have hd := low_base_bounds
  have hw : 0 < lowUpperLog 3100 - lowerLog 3100 := by linarith [hd.2.2]
  have hs := loglogShift_bounds hL
  have hs0 := hs.1
  have ht : 1 ≤ L / 3100 := by linarith
  have hl := Real.log_nonneg ht
  let r := (y - lowerLog 3100) / (lowUpperLog 3100 - lowerLog 3100)
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hy.1) hw.le
  have hr1 : r ≤ 1 := (div_le_iff₀ hw).mpr (by linarith [hy.2])
  have he : lowAffineSlope L * y + lowAffineOffset L =
      y + 3 * Real.log (L / 3100) + loglogShift L * r := by
    unfold lowAffineOffset lowAffineSlope
    rw [(source_log_scaling hL).1]
    dsimp [r]
    ring
  by_cases hz : Real.log (L / 3100) = 0
  · have hd0 : loglogShift L = 0 := by linarith
    refine ⟨3, by norm_num, by norm_num, ?_⟩
    rw [he, hd0, hz]
    ring
  · have hl0 : 0 < Real.log (L / 3100) := lt_of_le_of_ne hl (Ne.symm hz)
    let k := 3 + loglogShift L * r / Real.log (L / 3100)
    have hk0 : 0 ≤ k := by dsimp [k]; positivity
    have hkr : loglogShift L * r / Real.log (L / 3100) ≤ 1 := by
      apply (div_le_iff₀ hl0).mpr
      nlinarith
    refine ⟨k, hk0, by dsimp [k]; linarith, ?_⟩
    rw [he]
    dsimp [k]
    field_simp
    ring

end LiuWang.Proof.Campaign20260915.SecondLow
