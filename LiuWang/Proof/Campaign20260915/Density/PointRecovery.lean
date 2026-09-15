import LiuWang.Proof.Campaign20260915.Density.PointNumerical
import LiuWang.Proof.SourceRoute.Density.Restart.FamilyMaximum

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

theorem cosh_near_half_sq_sharp {x : ℝ}
    (hx0 : 0.4999 ≤ x) (hx1 : x ≤ 0.5001) :
    Real.cosh x ^ 2 ≤ 1.2722 := by
  have heU := Real.exp_bound' (x := 0.5001) (by norm_num) (by norm_num)
    (n := 8) (by norm_num)
  have heL := Real.sum_le_exp_of_nonneg (x := 0.4999) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at heU heL
  have hmU := Real.exp_le_exp.mpr hx1
  have hmL := Real.exp_le_exp.mpr hx0
  have hu : Real.exp x ≤ 1.649 := by linarith
  have hl : 1 / 0.6066 ≤ Real.exp x := by linarith
  have hn : Real.exp (-x) ≤ 0.6066 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos x)).mpr
    linarith
  have hc : Real.cosh x ≤ 1.1278 := by
    rw [Real.cosh_eq]
    linarith
  nlinarith [Real.cosh_pos x]

theorem source_cosine_equation_19 {y : ℝ} (hy : 10000 ≤ y)
    {s : ℂ} (ht : |s.im - y| ≤ 3 / 2) :
    ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 ≤ 1.2722 := by
  have hi : (s / (2 * (y : ℂ))).im = s.im / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
  have ht' := abs_le.mp ht
  have hc : Real.cosh (s.im / (2 * y)) ^ 2 ≤ 1.2722 := by
    apply cosh_near_half_sq_sharp
    · apply (le_div_iff₀ (by positivity : 0 < 2 * y)).mpr
      linarith
    · apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
      linarith
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (GlobalZeroDensity.Strip.norm_cos_le_cosh (s / (2 * (y : ℂ)))) 2
  rw [hi] at h
  exact h.trans hc

theorem source_family_lemma_11 (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y : ℝ} {s : ℂ} (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : s.re ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y)))
    (ht : |s.im - y| ≤ 3 / 2) :
    familySquare q ((q : ℝ) * y) s ≤
      47.202 * chenPointScale q y ^ (2 * (1 - s.re)) *
        Real.log ((q : ℝ) * y) ^ (8 * s.re - 4) := by
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hd := source_product_shift_bounds q hy
  have hsa : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2, hd.2]⟩
  have hpoint (chi : Interfaces.Character q) :
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) s‖ ^ 2 ≤
        1.2722 * ‖cosineDetector chi ((q : ℝ) * y) y s‖ ^ 2 := by
    have he : NonprincipalDensityAdvance.f chi ((q : ℝ) * y) s =
        cosineDetector chi ((q : ℝ) * y) y s * Complex.cos (s / (2 * (y : ℂ))) := by
      rw [cosineDetector, div_mul_cancel₀ _
        (cosine_denominator_extended (by linarith : 2 ≤ y) hsa)]
    conv_lhs => rw [he, norm_mul, mul_pow]
    exact (mul_le_mul_of_nonneg_left (source_cosine_equation_19 hy' ht)
      (sq_nonneg _)).trans_eq (mul_comm _ _)
  have h := sum_le_sum (s := nonprincipalCharacters q) (fun chi _ => hpoint chi)
  rw [← mul_sum] at h
  have hm := mul_le_mul_of_nonneg_left (source_family_point_equation_18 q hq hy hs)
    (by norm_num : (0 : ℝ) ≤ 1.2722)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1 ≤ q))
  have hL : 0 ≤ Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
  have hD : 0 ≤ chenPointScale q y := by unfold chenPointScale; positivity
  have hp := mul_nonneg (Real.rpow_nonneg hD (2 * (1 - s.re)))
    (Real.rpow_nonneg hL (8 * s.re - 4))
  unfold familySquare
  unfold chenPointBound at hm
  nlinarith only [h, hm, hp]

end LiuWang.Proof.Campaign20260915.Density
