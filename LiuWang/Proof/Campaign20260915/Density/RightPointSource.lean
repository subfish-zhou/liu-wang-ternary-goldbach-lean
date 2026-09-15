import LiuWang.Proof.Campaign20260915.Density.RightPoint
import LiuWang.Proof.Campaign20260915.Density.CosinePoint

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

theorem chen_exp_neg_four_thirds : Real.exp (-4 / 3) ≤ 0.27 := by
  have h := Real.sum_le_exp_of_nonneg (x := 4 / 3) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  rw [neg_div, Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

theorem source_right_point_scalar {X : ℝ} (hX : 0 < X) (hL : 11 ≤ Real.log X) :
    1.1 * X ^ (-2 * sourceDelta X) * (1 + 1 / sourceDelta X) ^ 4 ≤
      1.947 * Real.log X ^ 4 := by
  have hL0 : 0 < Real.log X := by linarith
  have he : X ^ (-2 * sourceDelta X) = Real.exp (-4 / 3) := by
    rw [Real.rpow_def_of_pos hX]
    congr 1
    unfold sourceDelta
    field_simp
    ring
  have hi : 1 / sourceDelta X = 1.5 * Real.log X := by
    unfold sourceDelta
    field_simp
  have hh : 1 + 1 / sourceDelta X ≤ 1.6 * Real.log X := by
    rw [hi]
    linarith
  have hn : 0 ≤ 1 + 1 / sourceDelta X := by rw [hi]; positivity
  rw [he]
  have h := mul_le_mul chen_exp_neg_four_thirds
    (pow_le_pow_left₀ hn hh 4) (pow_nonneg hn _) (by norm_num)
  have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1.1)
  nlinarith only [h', pow_nonneg hL0.le 4]

theorem source_complete_f_point_right (q : ℕ) [NeZero q] {y : ℝ} {s : ℂ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : 1 + sourceDelta ((q : ℝ) * y) ≤ s.re) :
    (∑ chi : Character q, ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) s‖ ^ 2) ≤
      1.947 * Real.log ((q : ℝ) * y) ^ 4 := by
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX : 11 * (q : ℝ) ≤ (q : ℝ) * y := by nlinarith
  have hd := source_product_shift_bounds q hy
  exact (complete_f_point_right q hX hd.1 (by linarith [hd.2]) hs).trans
    (source_right_point_scalar (by positivity) (source_product_log_ge_eleven q hy))

theorem source_family_point_right (q : ℕ) [NeZero q] {y : ℝ} {s : ℂ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : s.re = 1 + sourceDelta ((q : ℝ) * y)) :
    (∑ chi ∈ nonprincipalCharacters q,
      ‖cosineDetector chi ((q : ℝ) * y) y s‖ ^ 2) ≤
      2 * Real.log ((q : ℝ) * y) ^ 4 := by
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hd := source_product_shift_bounds q hy
  have hsa : |s.re| ≤ 2 := by rw [hs]; exact abs_le.mpr ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hraw : (∑ chi ∈ nonprincipalCharacters q,
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) s‖ ^ 2) ≤
      1.947 * Real.log ((q : ℝ) * y) ^ 4 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans
      (source_complete_f_point_right q hy hs.ge)
  have h := mul_le_mul hraw (source_cosine_point_inverse hy' hsa)
    (by positivity : 0 ≤ 1 / ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2)
    (by positivity : 0 ≤ 1.947 * Real.log ((q : ℝ) * y) ^ 4)
  simp_rw [cosineDetector, norm_div, div_pow]
  rw [← sum_div]
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  nlinarith only [h, sq_nonneg (Real.log ((q : ℝ) * y) ^ 2)]

end LiuWang.Proof.Campaign20260915.Density
