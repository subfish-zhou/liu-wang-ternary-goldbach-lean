import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.SmallHeight
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.MollifierInterpolation

/-! LWD p.285, (3.41), consuming the proved (3.39) and original (3.40). -/

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh

theorem interpolated_coefficient {theta : ℝ} (ht : theta ∈ Icc 0 1) :
    (1.3071 : ℝ) ^ (1 - theta) * (1.19 : ℝ) ^ theta ≤ 1.3071 := by
  have hm := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1.19)
    (by norm_num : (1.19 : ℝ) ≤ 1.3071) ht.1
  calc
    _ ≤ (1.3071 : ℝ) ^ (1 - theta) * (1.3071 : ℝ) ^ theta :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_one]

theorem interpolation_scale_lower {A L theta : ℝ}
    (hA : 9 ≤ A) (hL : 9 ≤ L) (ht : theta ∈ Icc 0 1) :
    81 ≤ A ^ (1 - theta) * L ^ (theta + 1) := by
  have h1 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 9) hA
    (show 0 ≤ 1 - theta by linarith [ht.2])
  have h2 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 9) hL ht.1
  have hm := mul_le_mul h1 h2 (by positivity) (by positivity)
  rw [← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_one] at hm
  have hprod := mul_le_mul hm hL (by norm_num : (0 : ℝ) ≤ 9) (by positivity)
  rw [Real.rpow_add (by linarith : 0 < L), Real.rpow_one]
  nlinarith only [hprod]

theorem product_bound_scalar {A L theta : ℝ}
    (hA : 9 ≤ A) (hL : 9 ≤ L) (ht : theta ∈ Icc 0 1) :
    (1.5 * L * ((1.3071 * A) ^ (1 - theta) * (1.19 * L) ^ theta) + 1) ^ 2 ≤
      4.255 * (A ^ (1 - theta) * L ^ (theta + 1)) ^ 2 := by
  let H := A ^ (1 - theta) * L ^ (theta + 1)
  have hH : 81 ≤ H := interpolation_scale_lower hA hL ht
  have heq :
      1.5 * L * ((1.3071 * A) ^ (1 - theta) * (1.19 * L) ^ theta) =
        1.5 * ((1.3071 : ℝ) ^ (1 - theta) * (1.19 : ℝ) ^ theta) * H := by
    rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ A),
      Real.mul_rpow (by norm_num) (by linarith : 0 ≤ L)]
    dsimp [H]
    rw [Real.rpow_add (by linarith : 0 < L), Real.rpow_one]
    ring
  rw [heq]
  have hc := mul_le_mul_of_nonneg_right (interpolated_coefficient ht)
    (show 0 ≤ H by linarith)
  have hmain : 1.5 * ((1.3071 : ℝ) ^ (1 - theta) * (1.19 : ℝ) ^ theta) * H + 1 ≤
      2.06 * H := by nlinarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤
    1.5 * ((1.3071 : ℝ) ^ (1 - theta) * (1.19 : ℝ) ^ theta) * H + 1) hmain 2
  change _ ≤ 4.255 * H ^ 2
  nlinarith [sq_nonneg H]

theorem source_scale_square {y sigma : ℝ} (hy : 0 < y) (hl : 0 < Real.log y) :
    ((Real.sqrt y) ^ (1 - (2 * sigma - 1)) *
      (Real.log y) ^ ((2 * sigma - 1) + 1)) ^ 2 =
      y ^ (2 * (1 - sigma)) * (Real.log y) ^ (4 * sigma) := by
  rw [mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hy.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hl.le]
  congr 1 <;> congr 1 <;> ring

theorem F_small_height_from_chen {y sigma t : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) (ht : |t| ≤ 1)
    (hchen11 : ∀ u : ℝ, ‖Q y ((1 / 2 : ℂ) + u * I)‖ ≤ 1.3071 * Real.sqrt y)
    (hchen12 : ∀ u : ℝ, ‖Q y ((1 : ℂ) + u * I)‖ ≤ 1.19 * Real.log y) :
    F y ((sigma : ℂ) + t * I) ≤
      4.255 * y ^ (2 * (1 - sigma)) * (Real.log y) ^ (4 * sigma) := by
  obtain ⟨hy', hl⟩ := source_height_log_bounds hy
  have hd : 0 < sourceDelta y := by unfold sourceDelta; positivity
  have hs' : sigma ∈ Icc (1 / 2) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have htheta : 2 * sigma - 1 ∈ Icc 0 1 := by
    constructor <;> linarith [hs'.1, hs'.2]
  have hroot : 9 ≤ Real.sqrt y := by
    have he := Real.sq_sqrt (show 0 ≤ y by linarith)
    nlinarith [Real.sqrt_nonneg y]
  have hscalar := product_bound_scalar hroot (show 9 ≤ Real.log y by linarith) htheta
  rw [source_scale_square (by linarith) (by linarith)] at hscalar
  have hz := zeta_small_height hy hs ht
  have hq := equation_3_40 hs' hchen11 hchen12 (t := t)
  have hp := mul_le_mul hz hq (norm_nonneg _) (by positivity)
  have hn := norm_sub_le
    (riemannZeta ((sigma : ℂ) + t * I) * Q y ((sigma : ℂ) + t * I)) 1
  rw [norm_mul, norm_one] at hn
  have hfn : ‖f y ((sigma : ℂ) + t * I)‖ ≤
      1.5 * Real.log y *
        ((1.3071 * Real.sqrt y) ^ (1 - (2 * sigma - 1)) *
          (1.19 * Real.log y) ^ (2 * sigma - 1)) + 1 := by
    rw [show 1 - (2 * sigma - 1) = 2 * (1 - sigma) by ring]
    change ‖riemannZeta _ * Q y _ - 1‖ ≤ _
    linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hfn 2
  unfold F
  exact (hsq.trans hscalar).trans_eq (by ring)

theorem equation_3_41 {y sigma : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y))
    (hchen11 : ∀ u : ℝ, ‖Q y ((1 / 2 : ℂ) + u * I)‖ ≤ 1.3071 * Real.sqrt y)
    (hchen12 : ∀ u : ℝ, ‖Q y ((1 : ℂ) + u * I)‖ ≤ 1.19 * Real.log y) :
    M y sigma 1 ≤ 2 * 4.255 * y ^ (2 * (1 - sigma)) * (Real.log y) ^ (4 * sigma) := by
  have hl := (source_height_log_bounds hy).2
  have hd : 0 < sourceDelta y := by unfold sourceDelta; positivity
  have hs1 : sigma ≠ 1 := by linarith [hs.2]
  have h := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
    (intervalIntegrable_F y 1 hs1) intervalIntegrable_const
    (fun t ht => F_small_height_from_chen hy hs (abs_le.mpr ht) hchen11 hchen12)
  rw [intervalIntegral.integral_const] at h
  change M y sigma 1 ≤ _ at h
  simp only [smul_eq_mul] at h
  linarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh
