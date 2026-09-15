import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.ScalarGeometry

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

def originalDensityScalar (L : ℝ) : ℝ :=
  8 * Real.exp (4 * 0.478) * sourceNu (L ^ (3 : ℕ)) * L *
    ∫ y in lowerLog L..upperLog L, densityKernel (L + Real.log 0.001) y

theorem affine_density_integrand_le {L y : ℝ} (hL : 3100 ≤ L)
    (hy : y ∈ Set.Icc (lowerLog 3100) (upperLog 3100)) :
    (sourceNu (L ^ (3 : ℕ)) * L * affineSlope L) *
      densityKernel (L + Real.log 0.001) (affineSlope L * y + affineOffset L) ≤
    (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
      densityKernel ((3100 : ℝ) + Real.log 0.001) y := by
  let t := L / 3100
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hLt : L = 3100 * t := by dsimp [t]; ring
  have hd := base_log_domain
  have hs := affine_source_domain hL
  have hnu := sourceNu_linear_scaling hL
  have hH := window_H_scaling hL
  have hHt : ((3100 : ℝ) + Real.log 0.001) * t ≤ L + Real.log 0.001 := hH.2
  have hnuBase : 0 ≤ sourceNu ((3100 : ℝ) ^ (3 : ℕ)) := hnu.1
  obtain ⟨k, hk0, hk7, he⟩ := affine_source_shift hL hy
  have hy20 : 20 ≤ y := hd.1.trans hy.1
  have hy60 : y ≤ 60 := hy.2.trans hd.2.1
  have hy0 : 0 < y := by linarith
  have hk := densityKernel_scaled hH.1 ht hH.2 hy20 hy60 hk0 hk7
  rw [he]
  have hb : 0 ≤ densityKernel ((3100 : ℝ) + Real.log 0.001) y := by
    have hden : 0 < (3100 : ℝ) + Real.log 0.001 - 4 * y := by linarith [hH.1]
    have hH0 : 0 < (3100 : ℝ) + Real.log 0.001 := by linarith [hH.1]
    unfold densityKernel
    positivity
  have hnu0 := (sourceNu_le_scaling hL).1
  have hcoef : sourceNu (L ^ (3 : ℕ)) * L * affineSlope L ≤
      (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) * t ^ (3 : ℕ) := by
    calc
      _ ≤ (t * sourceNu ((3100 : ℝ) ^ (3 : ℕ))) * (3100 * t) * t := by
        rw [← hLt]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hnu.2 (by linarith))
          hs.2.1 (by linarith [hs.1]) (by positivity)
      _ = _ := by ring
  have habs : t ^ (9 : ℕ) * Real.exp (-10.516 * Real.log t) ≤ 1 := by
    rw [← Real.exp_log ht0, ← Real.exp_nat_mul]
    rw [Real.exp_log ht0, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hl := Real.log_nonneg ht
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ ≤ ((sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) * t ^ (3 : ℕ)) *
        (t ^ (6 : ℕ) * Real.exp (-10.516 * Real.log t) *
          densityKernel ((3100 : ℝ) + Real.log 0.001) y) := by
      exact mul_le_mul hcoef hk (by
        have hz := shifted_height_bounds ht hy20 hk0 hk7
        have hz0 : 0 < y + k * Real.log t := hz.1
        have hHp : 0 < L + Real.log 0.001 := by nlinarith [hH.1, hH.2]
        have hden : 0 < L + Real.log 0.001 - 4 * (y + k * Real.log t) := by
          have hh := mul_pos (by linarith [hH.1] :
            0 < (3100 : ℝ) + Real.log 0.001 - 4 * y) ht0
          nlinarith only [hh, hHt, hz.2.2]
        unfold densityKernel
        positivity) (by positivity)
    _ = ((sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
        densityKernel ((3100 : ℝ) + Real.log 0.001) y) *
          (t ^ (9 : ℕ) * Real.exp (-10.516 * Real.log t)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left habs (by positivity)).trans_eq (mul_one _)

theorem originalDensityScalar_le_base {L : ℝ} (hL : 3100 ≤ L) :
    originalDensityScalar L ≤ originalDensityScalar 3100 := by
  have hd := base_log_domain
  have hs := affine_source_domain hL
  have hH := window_H_scaling hL
  have hLp : 0 < L := by linarith
  have ht : 1 ≤ L / 3100 := by linarith
  have ht0 : 0 < L / 3100 := by positivity
  have hab : lowerLog 3100 ≤ upperLog 3100 := by linarith [hd.2.2]
  have hcont : ContinuousOn
      (fun y => densityKernel (L + Real.log 0.001) (affineSlope L * y + affineOffset L))
      (Set.Icc (lowerLog 3100) (upperLog 3100)) := by
    have hz : ∀ y ∈ Set.Icc (lowerLog 3100) (upperLog 3100),
        affineSlope L * y + affineOffset L ≠ 0 := by
      intro y hy
      obtain ⟨k, hk0, hk7, he⟩ := affine_source_shift hL hy
      rw [he]
      exact (shifted_height_bounds ht (hd.1.trans hy.1) hk0 hk7).1.ne'
    have hden : ∀ y ∈ Set.Icc (lowerLog 3100) (upperLog 3100),
        L + Real.log 0.001 - 4 * (affineSlope L * y + affineOffset L) ≠ 0 := by
      intro y hy
      obtain ⟨k, hk0, hk7, he⟩ := affine_source_shift hL hy
      rw [he]
      have hh := shifted_height_bounds ht (hd.1.trans hy.1) hk0 hk7
      have hp := mul_pos (by linarith [hH.1, hy.2, hd.2.1] :
        0 < (3100 : ℝ) + Real.log 0.001 - 4 * y) ht0
      apply ne_of_gt
      nlinarith only [hp, hH.2, hh.2.2]
    unfold densityKernel
    have hf : ContinuousOn (fun y => affineSlope L * y + affineOffset L)
        (Set.Icc (lowerLog 3100) (upperLog 3100)) :=
      (continuousOn_const.mul continuousOn_id).add continuousOn_const
    exact ((((continuousOn_const.div hf hz).add continuousOn_const).mul (hf.pow 6)).mul
      (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul hf)) hden)).mul
      (Real.continuous_exp.comp_continuousOn
        (((hf.neg).div_const 2).sub (continuousOn_const.div hf hz)))
  have hbase : ContinuousOn (densityKernel ((3100 : ℝ) + Real.log 0.001))
      (Set.Icc (lowerLog 3100) (upperLog 3100)) := by
    have hz : ∀ y ∈ Set.Icc (lowerLog 3100) (upperLog 3100), y ≠ 0 :=
      fun y hy => ne_of_gt (by linarith [hd.1, hy.1])
    have hn : ∀ y ∈ Set.Icc (lowerLog 3100) (upperLog 3100),
        (3100 : ℝ) + Real.log 0.001 - 4 * y ≠ 0 :=
      fun y hy => ne_of_gt (by linarith [hH.1, hy.2, hd.2.1])
    unfold densityKernel
    exact ((((continuousOn_const.div continuousOn_id hz).add continuousOn_const).mul
      (continuousOn_id.pow 6)).mul
      (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) hn)).mul
      (Real.continuous_exp.comp_continuousOn
        (((continuousOn_id.neg).div_const 2).sub (continuousOn_const.div continuousOn_id hz)))
  have hi := intervalIntegral.integral_mono_on hab
    ((hcont.const_mul (sourceNu (L ^ (3 : ℕ)) * L * affineSlope L)).intervalIntegrable_of_Icc
      (μ := volume) hab)
    ((hbase.const_mul (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100)).intervalIntegrable_of_Icc
      (μ := volume) hab)
    (fun y hy => affine_density_integrand_le hL hy)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hchange := intervalIntegral.smul_integral_comp_mul_add
    (densityKernel (L + Real.log 0.001)) (a := lowerLog 3100) (b := upperLog 3100)
    (affineSlope L) (affineOffset L)
  simp only [smul_eq_mul] at hchange
  rw [hs.2.2.1, hs.2.2.2] at hchange
  rw [mul_assoc, hchange] at hi
  have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 8 * Real.exp (4 * 0.478))
  unfold originalDensityScalar
  nlinarith only [hm]

theorem original_510_fixed_certificate_iff :
    (∀ L : ℝ, 3100 ≤ L → originalDensityScalar L ≤ 0.032281) ↔
      originalDensityScalar 3100 ≤ 0.032281 := by
  constructor
  · intro h
    exact h 3100 le_rfl
  · intro h L hL
    exact (originalDensityScalar_le_base hL).trans h

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
