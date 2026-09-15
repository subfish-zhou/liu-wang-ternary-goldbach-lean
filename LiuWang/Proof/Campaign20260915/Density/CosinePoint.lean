import LiuWang.Proof.Campaign20260915.Density.PointwiseCritical
import LiuWang.Proof.Campaign20260915.Density.PointwiseKernel

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem norm_cos_sq_identity (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have hh := congrArg (fun x : ℝ => Real.cos z.re ^ 2 * x)
    (Real.cosh_sq_sub_sinh_sq z.im)
  have hc := congrArg (fun x : ℝ => Real.sinh z.im ^ 2 * x)
    (Real.sin_sq_add_cos_sq z.re)
  rw [Complex.cos_eq z, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh, Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, mul_zero, sub_zero,
    I_re, I_im, mul_one, sub_im, mul_im, add_zero, zero_sub, neg_mul_neg]
  nlinarith only [hh, hc]

theorem norm_cos_sq_doubled (z : ℂ) :
    4 * ‖Complex.cos z‖ ^ 2 =
      2 * Real.cosh (2 * z.im) + 2 * Real.cos (2 * z.re) := by
  rw [norm_cos_sq_identity]
  nlinarith only [Real.cosh_two_mul z.im, Real.cosh_sq_sub_sinh_sq z.im,
    Real.cos_two_mul z.re]

theorem source_cosine_point_denominator {y : ℝ} (hy : 10000 ≤ y)
    {s : ℂ} (hs : |s.re| ≤ 2) :
    Real.exp (|s.im| / y) + Real.exp (- (|s.im| / y)) + 2 ≤
      4.001 * ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hr : |s.re / y| ≤ 0.0002 := by
    rw [abs_div, abs_of_pos hy0]
    apply (div_le_iff₀ hy0).mpr
    linarith
  have hcos : 0.9999 ≤ Real.cos (s.re / y) := by
    have hsq := (sq_le_sq₀ (abs_nonneg (s.re / y)) (by norm_num)).mpr hr
    rw [sq_abs] at hsq
    linarith [Real.one_sub_sq_div_two_le_cos (x := s.re / y)]
  have hi : 2 * (s / (2 * (y : ℂ))).im = s.im / y := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    ring
  have hre : 2 * (s / (2 * (y : ℂ))).re = s.re / y := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    ring
  have h := norm_cos_sq_doubled (s / (2 * (y : ℂ)))
  rw [hi, hre] at h
  have habs : Real.cosh (s.im / y) = Real.cosh (|s.im| / y) := by
    simpa only [abs_div, abs_of_pos hy0] using (Real.cosh_abs (s.im / y)).symm
  rw [habs, Real.cosh_eq] at h
  have hge := Real.one_le_cosh (|s.im| / y)
  rw [Real.cosh_eq] at hge
  linarith

theorem source_cosine_point_inverse {y : ℝ} (hy : 10000 ≤ y)
    {s : ℂ} (hs : |s.re| ≤ 2) :
    1 / ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 ≤ 1.001 := by
  have h := source_cosine_point_denominator hy hs
  have hc := Real.one_le_cosh (|s.im| / y)
  rw [Real.cosh_eq] at hc
  have hd : 0 < ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 := by linarith
  apply (div_le_iff₀ hd).mpr
  linarith

theorem source_cosine_point_linear {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    (2 + |t|) / ‖Complex.cos (((1 / 2 : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 ≤
      0.904 * y := by
  let u : ℝ := |t| / y
  let E : ℝ := Real.exp u + Real.exp (-u) + 2
  let D : ℝ := ‖Complex.cos (((1 / 2 : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2
  have hy0 : 0 < y := by linarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hden : E ≤ 4.001 * D := by
    simpa [E, u, D] using source_cosine_point_denominator hy
      (s := (1 / 2 : ℂ) + t * I) (by norm_num)
  have hfour : 4 ≤ E := by
    have h := Real.one_le_cosh u
    rw [Real.cosh_eq] at h
    dsimp [E]
    linarith
  have hD : 0 < D := by linarith
  have hlogistic := (div_le_iff₀ hE).mp (logistic_point_kernel hu)
  have ht : |t| ≤ 0.225 * y * E := by
    have h := mul_le_mul_of_nonneg_left hlogistic hy0.le
    dsimp [u] at h
    rw [mul_div_cancel₀ _ hy0.ne'] at h
    nlinarith only [h]
  have hone : 2 ≤ 0.00005 * y * E := by
    have h := mul_le_mul_of_nonneg_left hfour (show 0 ≤ 0.00005 * y by positivity)
    nlinarith only [h, hy]
  have h := mul_le_mul_of_nonneg_left hden (show 0 ≤ 0.22505 * y by positivity)
  change (2 + |t|) / D ≤ 0.904 * y
  apply (div_le_iff₀ hD).mpr
  nlinarith only [ht, hone, h, mul_nonneg hy0.le hD.le]

theorem source_family_point_critical (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (t : ℝ) :
    (∑ chi ∈ nonprincipalCharacters q,
      ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      37.1 * Real.sqrt q * ((q : ℝ) * y) * y * Real.log q := by
  let C : ℝ := 41.00096 * (q : ℝ) * Real.sqrt q * y * Real.log q
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy0 : 0 ≤ y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : 1 ≤ Real.log q := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (Nat.cast_le.mpr hq)
    linarith [Real.log_three_gt_d9]
  have hs : (1 : ℝ) ≤ Real.sqrt q :=
    (Real.le_sqrt (by norm_num) hq0.le).mpr (by exact_mod_cast (by omega : 1 ≤ q))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hraw := div_le_div_of_nonneg_right (family_point_critical q hy t)
    (sq_nonneg ‖Complex.cos (((1 / 2 : ℂ) + t * I) / (2 * (y : ℂ)))‖)
  have hlin := mul_le_mul_of_nonneg_left (source_cosine_point_linear hy' t) hC
  have hinv := mul_le_mul_of_nonneg_left
    (source_cosine_point_inverse hy' (s := (1 / 2 : ℂ) + t * I) (by norm_num))
    (show 0 ≤ 1001 * (q : ℝ) by positivity)
  have hm : 1 ≤ Real.sqrt q * Real.log q := one_le_mul_of_one_le_of_one_le hs hl
  have hmain := mul_le_mul_of_nonneg_left hm (show 0 ≤ (q : ℝ) * y ^ 2 by positivity)
  have hry : 200200 ≤ y ^ 2 := by nlinarith
  have hr := mul_le_mul_of_nonneg_left hry hq0.le
  simp_rw [cosineDetector, norm_div, div_pow]
  rw [← sum_div]
  dsimp [C] at hlin
  simp only [div_eq_mul_inv] at hraw hlin hinv ⊢
  nlinarith only [hraw, hlin, hinv, hmain, hr]

end LiuWang.Proof.Campaign20260915.Density
