import LiuWang.Proof.Campaign20260915.Density.DensityScale

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_cosine_enlarged_window {y : ℝ} (hy : 10000 ≤ y)
    {s : ℂ} (ht : |s.im| ≤ y + 3 / 2) :
    ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 ≤ 1.2722 := by
  have hi : |(s / (2 * (y : ℂ))).im| ≤ 0.5001 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im,
      abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hc := Real.cosh_le_cosh.mpr
    (show |(s / (2 * (y : ℂ))).im| ≤ |(0.5001 : ℝ)| by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 0.5001)] using hi)
  exact (pow_le_pow_left₀ (norm_nonneg _)
    ((GlobalZeroDensity.Strip.norm_cos_le_cosh _).trans hc) 2).trans
      (cosh_near_half_sq_sharp (by norm_num) le_rfl)

theorem source_familyMean_enlarged (q : ℕ) [NeZero q] {y sigma U : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y)))
    (hU : 0 ≤ U) (hUy : U ≤ y + 3 / 2) :
    familyMean q ((q : ℝ) * y) sigma U ≤ 1.2722 * chenInterpolatedBound q y sigma := by
  have hy' := source_height_ge_ten_thousand hy
  have hy2 : 2 ≤ y := by linarith
  have hd := source_product_shift_bounds q hy
  have hs2 : sigma ∈ Set.Icc (1 / 2) 2 := ⟨hs.1, by linarith [hs.2, hd.2]⟩
  have hsa : |sigma| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1], hs2.2⟩
  have hw (chi : Interfaces.Character q) (hc : chi ∈ nonprincipalCharacters q) :
      (∫ t in -U..U, ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y)
        ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      1.2722 * (∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) := by
    have hn := (NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc
    have hfi := NonprincipalDensityMeans.f_vertical_integrable hn ((q : ℝ) * y) sigma U
    have hg := cosine_integrable_extended hn ((q : ℝ) * y) hy2 hs2
    have hgi : IntervalIntegrable (fun t : ℝ =>
        ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) volume (-U) U :=
      ((cosine_vertical_continuous_extended hn ((q : ℝ) * y) hy2 hsa).norm.pow 2).intervalIntegrable (-U) U
    have hp := intervalIntegral.integral_mono_on (by linarith : -U ≤ U) hfi
      (hgi.const_mul 1.2722) (fun t ht => by
        have hst : |(((sigma : ℂ) + t * I).im)| ≤ y + 3 / 2 := by
          simpa using (abs_le.mpr ht).trans hUy
        have he : NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((sigma : ℂ) + t * I) =
            cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I) *
              Complex.cos (((sigma : ℂ) + t * I) / (2 * (y : ℂ))) := by
          rw [cosineDetector, div_mul_cancel₀ _
            (cosine_denominator_extended hy2 (by simpa using hsa))]
        conv_lhs => rw [he, norm_mul, mul_pow]
        exact (mul_le_mul_of_nonneg_left (source_cosine_enlarged_window hy' hst)
          (sq_nonneg _)).trans_eq (mul_comm _ _))
    rw [intervalIntegral.integral_const_mul] at hp
    have hw : (∫ t in -U..U, ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
        ∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral hg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    exact hp.trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  have h := sum_le_sum (s := nonprincipalCharacters q) hw
  rw [← mul_sum] at h
  unfold familyMean familySquare
  rw [intervalIntegral.integral_finsetSum]
  · exact h.trans (mul_le_mul_of_nonneg_left (source_family_equation_32 q hy hs) (by norm_num))
  · intro chi hc
    exact NonprincipalDensityMeans.f_vertical_integrable
      ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc) _ _ _

theorem source_vertical_main_enlarged (q : ℕ) [NeZero q] {y alpha U : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ alpha) (ha1 : alpha ≤ 1)
    (hU : 0 ≤ U) (hUy : U ≤ y + 3 / 2) :
    familyMean q ((q : ℝ) * y) (alpha - sourceDelta ((q : ℝ) * y)) U /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 5699 * chenDensityScale q y alpha := by
  have hd := (source_product_shift_bounds q hy).1
  have hm := source_familyMean_enlarged q hy
    (sigma := alpha - sourceDelta ((q : ℝ) * y)) ⟨by linarith, by linarith⟩ hU hUy
  apply (div_le_div_of_nonneg_right hm (by positivity)).trans
  have he : (1.2722 * chenInterpolatedBound q y (alpha - sourceDelta ((q : ℝ) * y))) /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) =
      (1.2722 / 1.272) * ((1.272 * chenInterpolatedBound q y
        (alpha - sourceDelta ((q : ℝ) * y))) / (2 * Real.pi * sourceDelta ((q : ℝ) * y))) := by ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (source_vertical_main_scalar q hy ha ha1)
    (by norm_num : (0 : ℝ) ≤ 1.2722 / 1.272)
  nlinarith only [h, (source_density_scale_pos q hy alpha).le]

theorem source_vertical_right_enlarged (q : ℕ) [NeZero q] {y U : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hU : 0 ≤ U) (hUy : U ≤ y + 3 / 2) :
    (3 / 2) * familyMean q ((q : ℝ) * y) 2 U /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 1 := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  let d : ℝ := sourceDelta X
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy' := source_height_ge_ten_thousand hy
  have hX : 100000 ≤ X := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    dsimp [X]
    nlinarith only [h]
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hXm : 0 < X - 1 := by linarith
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have hphi : ((q.totient - 1 : ℕ) : ℝ) ≤ q :=
    Nat.cast_le.mpr ((Nat.sub_le _ _).trans (Nat.totient_le q))
  have hm := mul_le_mul_of_nonneg_left (familyMean_two_le q (X := X) (by linarith) hU)
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  have hQU : (q : ℝ) * U ≤ 1.001 * X := by
    have h := mul_le_mul_of_nonneg_left (show U ≤ 1.001 * y by linarith) hq0.le
    dsimp [X]
    nlinarith only [h]
  have hp := mul_le_mul_of_nonneg_left hphi (show 0 ≤ 12 * U / (X - 1) ^ 2 by positivity)
  have hp' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQU
    (by norm_num : (0 : ℝ) ≤ 12)) (sq_nonneg (X - 1))
  have hraw : (3 / 2) * familyMean q X 2 U ≤ 12.012 * X / (X - 1) ^ 2 := by
    simp only [div_eq_mul_inv] at hm hp hp' ⊢
    nlinarith only [hm, hp, hp']
  have he : (12.012 * X / (X - 1) ^ 2) / (2 * Real.pi * d) =
      9.009 * X * L / (Real.pi * (X - 1) ^ 2) := by
    dsimp only [d, sourceDelta]
    change (12.012 * X / (X - 1) ^ 2) / (2 * Real.pi * (1 / (1.5 * L))) = _
    field_simp
    ring
  apply ((div_le_div_of_nonneg_right hraw (by positivity)).trans_eq he).trans
  apply (div_le_iff₀ (by positivity : 0 < Real.pi * (X - 1) ^ 2)).mpr
  have hl := mul_le_mul_of_nonneg_left (log_le_quarter (by linarith : 11 ≤ X))
    (show 0 ≤ 9.009 * X by linarith)
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg (X - 1))
  have hx := mul_nonneg (show 0 ≤ X by linarith) (show 0 ≤ X - 100 by linarith)
  dsimp [L]
  nlinarith only [hl, hp, hx]

theorem source_vertical_enlarged (q : ℕ) [NeZero q] {y alpha U : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ alpha) (ha1 : alpha ≤ 1)
    (hU : 0 ≤ U) (hUy : U ≤ y + 3 / 2) :
    (familyMean q ((q : ℝ) * y) (alpha - sourceDelta ((q : ℝ) * y)) U +
      (3 / 2) * familyMean q ((q : ℝ) * y) 2 U) /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 5700 * chenDensityScale q y alpha := by
  have hscale := source_density_scale_ge_log_six q hy ha1
  have hL := source_product_log_ge_eleven q hy
  have h1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * y) ^ (6 : ℕ) := one_le_pow₀ (by linarith)
  rw [add_div]
  nlinarith only [source_vertical_main_enlarged q hy ha ha1 hU hUy,
    source_vertical_right_enlarged q hy hU hUy, hscale, h1]

end LiuWang.Proof.Campaign20260915.Density
