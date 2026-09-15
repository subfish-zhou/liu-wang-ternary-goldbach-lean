import LiuWang.Proof.Campaign20260915.SecondLow.Geometry

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.Campaign20260915.SecondLow

open SourceRoute.SecondArc.Continuation
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem lowLogKernel_nonneg {L y : ℝ} (hL : 3100 ≤ L) (hy : 20 ≤ y) :
    0 ≤ lowLogKernel L y := by
  have hlog : 7 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hL0 : 0 < L := by linarith
  have hc : 0 ≤ (y + 3 * Real.log L) / Real.pi - 0.874 := by
    have hh : 0.874 ≤ (y + 3 * Real.log L) / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
    linarith
  have hp : 0 ≤ 6.8423 * (y + 3 * Real.log L) + 15 := by linarith
  unfold lowLogKernel
  positivity

theorem lowLogKernel_continuousOn (L : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (lowLogKernel L) (Set.Icc u v) := by
  have hz : ∀ y ∈ Set.Icc u v, y ≠ 0 := fun y hy => (hu.trans_le hy.1).ne'
  have ha : ContinuousOn (fun y : ℝ => y + 3 * Real.log L) (Set.Icc u v) :=
    continuousOn_id.add continuousOn_const
  have he : ContinuousOn (fun y : ℝ => 0.478 * (L + Real.log 0.001) / y)
      (Set.Icc u v) := continuousOn_const.div continuousOn_id hz
  exact ((continuousOn_const.mul ((ha.div_const Real.pi).sub continuousOn_const)).mul
    (Real.continuous_exp.comp_continuousOn ((continuousOn_id.div_const 2).sub he))).add
    ((continuousOn_const.mul ((continuousOn_const.mul ha).add continuousOn_const)).mul
      (Real.continuous_exp.comp_continuousOn ((continuousOn_id.neg.div_const 2).sub he)))

theorem power_exp_absorption {t d : ℝ} (ht : 1 ≤ t) (n : ℕ)
    (hd : (n : ℝ) ≤ d) :
    t ^ n * Real.exp (-d * Real.log t) ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have hp : t ^ n = Real.exp ((n : ℝ) * Real.log t) := by
    rw [Real.exp_nat_mul, Real.exp_log ht0]
  rw [hp, ← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.log_nonneg ht]

theorem shifted_lowLogKernel_bound {L y k : ℝ} (hL : 3100 ≤ L)
    (hy : 20 ≤ y) (hy60 : y ≤ 60) (hk : 0 ≤ k) (hk7 : k ≤ 7) :
    (L / 3100) * lowLogKernel L (y + k * Real.log (L / 3100)) ≤
      lowLogKernel 3100 y := by
  let t := L / 3100
  let z := y + k * Real.log t
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hLt : L = 3100 * t := by dsimp [t]; ring
  have hl := Real.log_nonneg ht
  have hlt := Real.log_le_sub_one_of_pos ht0
  have hb := log_3100_bounds.1
  have hlog : Real.log L = Real.log (3100 : ℝ) + Real.log t := by
    dsimp [t]
    rw [Real.log_div hL0.ne' (by norm_num)]
    ring
  have hz := shifted_height_bounds ht hy hk hk7
  have hg := shifted_phase_gain (window_H_scaling hL).1 ht
    (window_H_scaling hL).2 hy hy60 hk hk7
  have hkl : k * Real.log t ≤ 7 * Real.log t :=
    mul_le_mul_of_nonneg_right hk7 hl
  have hnum : z + 3 * Real.log L - 0.874 * Real.pi ≤
      t * (y + 3 * Real.log (3100 : ℝ) - 0.874 * Real.pi) := by
    have hp := mul_nonneg (sub_nonneg.mpr ht)
      (by linarith [Real.pi_lt_d2] :
        0 ≤ y + 3 * Real.log (3100 : ℝ) - 0.874 * Real.pi - 10)
    dsimp [z]
    rw [hlog]
    nlinarith only [hp, hlt, hkl]
  have hmain : (z + 3 * Real.log L) / Real.pi - 0.874 ≤
      t * ((y + 3 * Real.log (3100 : ℝ)) / Real.pi - 0.874) := by
    have he (a : ℝ) : a / Real.pi - 0.874 = (a - 0.874 * Real.pi) / Real.pi := by
      field_simp
    rw [he, he, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hnum Real.pi_pos.le
  have hpoly : 6.8423 * (z + 3 * Real.log L) + 15 ≤
      t * (6.8423 * (y + 3 * Real.log (3100 : ℝ)) + 15) := by
    have hp := mul_nonneg (sub_nonneg.mpr ht)
      (by linarith : 0 ≤ 6.8423 * (y + 3 * Real.log (3100 : ℝ)) + 15 - 68.423)
    dsimp [z]
    rw [hlog]
    nlinarith only [hp, hlt, hkl]
  have ha0 : 0 ≤ (y + 3 * Real.log (3100 : ℝ)) / Real.pi - 0.874 := by
    have hh : 0.874 ≤ (y + 3 * Real.log (3100 : ℝ)) / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
    linarith
  have hb0 : 0 ≤ 6.8423 * (y + 3 * Real.log (3100 : ℝ)) + 15 := by linarith
  have he1 : Real.exp (z / 2 - 0.478 * (L + Real.log 0.001) / z) ≤
      Real.exp (-7.016 * Real.log t) *
        Real.exp (y / 2 - 0.478 * (3100 + Real.log 0.001) / y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [z]
    simp only [div_eq_mul_inv] at hg ⊢
    nlinarith only [hg, hkl]
  have he2 : Real.exp (-z / 2 - 0.478 * (L + Real.log 0.001) / z) ≤
      Real.exp (-10.516 * Real.log t) *
        Real.exp (-y / 2 - 0.478 * (3100 + Real.log 0.001) / y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [z]
    simp only [div_eq_mul_inv] at hg ⊢
    nlinarith only [hg, hz.2.1]
  have hm1 : t * (L * ((z + 3 * Real.log L) / Real.pi - 0.874) *
      Real.exp (z / 2 - 0.478 * (L + Real.log 0.001) / z)) ≤
      3100 * ((y + 3 * Real.log (3100 : ℝ)) / Real.pi - 0.874) *
        Real.exp (y / 2 - 0.478 * (3100 + Real.log 0.001) / y) := by
    calc
      _ ≤ t * (L * (t * ((y + 3 * Real.log (3100 : ℝ)) / Real.pi - 0.874)) *
          (Real.exp (-7.016 * Real.log t) *
            Real.exp (y / 2 - 0.478 * (3100 + Real.log 0.001) / y))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hmain hL0.le) he1
            (Real.exp_pos _).le (by positivity)) ht0.le
      _ = (3100 * ((y + 3 * Real.log (3100 : ℝ)) / Real.pi - 0.874) *
          Real.exp (y / 2 - 0.478 * (3100 + Real.log 0.001) / y)) *
            (t ^ (3 : ℕ) * Real.exp (-7.016 * Real.log t)) := by rw [hLt]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (power_exp_absorption ht 3 (by norm_num)) (by positivity)).trans_eq (mul_one _)
  have hm2 : t * (L * L ^ (3 : ℕ) * (6.8423 * (z + 3 * Real.log L) + 15) *
      Real.exp (-z / 2 - 0.478 * (L + Real.log 0.001) / z)) ≤
      3100 * (3100 : ℝ) ^ (3 : ℕ) *
        (6.8423 * (y + 3 * Real.log (3100 : ℝ)) + 15) *
        Real.exp (-y / 2 - 0.478 * (3100 + Real.log 0.001) / y) := by
    calc
      _ ≤ t * (L * L ^ (3 : ℕ) *
          (t * (6.8423 * (y + 3 * Real.log (3100 : ℝ)) + 15)) *
          (Real.exp (-10.516 * Real.log t) *
            Real.exp (-y / 2 - 0.478 * (3100 + Real.log 0.001) / y))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) he2
            (Real.exp_pos _).le (by positivity)) ht0.le
      _ = (3100 * (3100 : ℝ) ^ (3 : ℕ) *
          (6.8423 * (y + 3 * Real.log (3100 : ℝ)) + 15) *
          Real.exp (-y / 2 - 0.478 * (3100 + Real.log 0.001) / y)) *
            (t ^ (6 : ℕ) * Real.exp (-10.516 * Real.log t)) := by rw [hLt]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (power_exp_absorption ht 6 (by norm_num)) (by positivity)).trans_eq (mul_one _)
  change t * lowLogKernel L z ≤ lowLogKernel 3100 y
  unfold lowLogKernel
  rw [mul_add]
  exact add_le_add hm1 hm2

theorem affine_low_integrand_le {L y : ℝ} (hL : 3100 ≤ L)
    (hy : y ∈ Set.Icc (lowerLog 3100) (lowUpperLog 3100)) :
    lowAffineSlope L * lowLogKernel L (lowAffineSlope L * y + lowAffineOffset L) ≤
      lowLogKernel 3100 y := by
  have hd := low_base_bounds
  have hy20 : 20 ≤ y := hd.1.trans hy.1
  have hy60 : y ≤ 60 := by linarith [hy.2, hd.2.1]
  have ht : 1 ≤ L / 3100 := by linarith
  obtain ⟨k, hk0, hk7, he⟩ := low_affine_shift hL hy
  rw [he]
  apply le_trans _ (shifted_lowLogKernel_bound hL hy20 hy60 hk0 hk7)
  exact mul_le_mul_of_nonneg_right (low_affine_domain hL).2.1
    (lowLogKernel_nonneg hL (hy20.trans (shifted_height_bounds ht hy20 hk0 hk7).2.1))

theorem originalLowScalar_le_base {L : ℝ} (hL : 3100 ≤ L) :
    originalLowScalar L ≤ originalLowScalar 3100 := by
  have hd := low_base_bounds
  have hab : lowerLog 3100 ≤ lowUpperLog 3100 := by linarith [hd.2.2]
  have hs := low_affine_domain hL
  have hu : 0 < lowerLog 3100 := by linarith [hd.1]
  have huL : 0 < lowerLog L := by
    rw [(source_log_scaling hL).1]
    have ht : 1 ≤ L / 3100 := by linarith
    linarith [Real.log_nonneg ht]
  have hmaps : Set.MapsTo (fun y => lowAffineSlope L * y + lowAffineOffset L)
      (Set.Icc (lowerLog 3100) (lowUpperLog 3100)) (Set.Icc (lowerLog L) (lowUpperLog L)) := by
    intro y hy
    constructor
    · rw [← hs.2.2.1]
      exact add_le_add (mul_le_mul_of_nonneg_left hy.1
        (by linarith [hs.1] : 0 ≤ lowAffineSlope L)) le_rfl
    · rw [← hs.2.2.2]
      exact add_le_add (mul_le_mul_of_nonneg_left hy.2
        (by linarith [hs.1] : 0 ≤ lowAffineSlope L)) le_rfl
  have hc := (lowLogKernel_continuousOn L huL).comp
    (by fun_prop : ContinuousOn (fun y : ℝ => lowAffineSlope L * y + lowAffineOffset L)
      (Set.Icc (lowerLog 3100) (lowUpperLog 3100))) hmaps
  have hi := intervalIntegral.integral_mono_on hab
    ((hc.const_mul (lowAffineSlope L)).intervalIntegrable_of_Icc (μ := volume) hab)
    ((lowLogKernel_continuousOn 3100 hu).intervalIntegrable_of_Icc (μ := volume) hab)
    (fun y hy => affine_low_integrand_le hL hy)
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp only [Function.comp_def] at hi
  have hchange := intervalIntegral.smul_integral_comp_mul_add (lowLogKernel L)
    (a := lowerLog 3100) (b := lowUpperLog 3100) (lowAffineSlope L) (lowAffineOffset L)
  simp only [smul_eq_mul] at hchange
  rw [hs.2.2.1, hs.2.2.2] at hchange
  rw [hchange] at hi
  rw [originalLowScalar_log hL, originalLowScalar_log (by norm_num)]
  exact hi

end LiuWang.Proof.Campaign20260915.SecondLow
