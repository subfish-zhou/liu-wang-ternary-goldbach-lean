import LiuWang.Proof.Campaign20260915.Density.FamilyRightLimit
import LiuWang.Proof.Campaign20260915.Density.Chen14

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

theorem family_right_error_polynomial {L : ℝ} (hL : 11 ≤ L) :
    4 * (3 * (1 + (3 / 4) * L) ^ 4 + (3 * L) * (1 + L) ^ 4) +
      (24 / 5) * (1 + (3 / 2) * L) ^ 5 ≤ 67 * L ^ 5 := by
  have h1 := pow_le_pow_left₀ (show 0 ≤ 1 + (3 / 4) * L by linarith)
    (show 1 + (3 / 4) * L ≤ (37 / 44) * L by linarith) 4
  have h2 := pow_le_pow_left₀ (show 0 ≤ 1 + L by linarith)
    (show 1 + L ≤ (12 / 11) * L by linarith) 4
  have h3 := pow_le_pow_left₀ (show 0 ≤ 1 + (3 / 2) * L by linarith)
    (show 1 + (3 / 2) * L ≤ (35 / 22) * L by linarith) 5
  have h4 : 11 * L ^ 4 ≤ L ^ 5 := by
    nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ L by linarith) 4)
      (show 0 ≤ L - 11 by linarith)]
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ L by linarith)
  norm_num [mul_pow] at h1 h3 h2'
  nlinarith only [h1, h2', h3, h4]

theorem source_shift_mass_decay {X : ℝ} (hX : 1 < X) :
    X ^ (-sourceDelta X) ≤ 3 / 5 := by
  have hL : 0 < Real.log X := Real.log_pos hX
  rw [Real.rpow_def_of_pos (by linarith : 0 < X)]
  have he : Real.log X * (-sourceDelta X) = -(2 / 3 : ℝ) := by
    unfold sourceDelta
    field_simp
    ring
  rw [he, Real.exp_neg]
  have hh : (5 / 3 : ℝ) ≤ Real.exp (2 / 3) := by
    linarith [Real.add_one_le_exp (2 / 3 : ℝ)]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 3) hh
  norm_num at h
  exact h

theorem full_nonprincipal_right_mean {q : ℕ} [NeZero q] {X u : ℝ}
    (hX : 2 * (q : ℝ) ≤ X) (hL : 11 ≤ Real.log X) (hu : 0 ≤ u) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -(X * u / q)..(X * u / q),
      ‖NonprincipalDensityAdvance.f chi X
        (((1 + sourceDelta X : ℝ) : ℂ) + t * I)‖ ^ 2) ≤
      (67.929 + 0.0003 * u) * Real.log X ^ 5 := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX1 : 1 < X := by linarith
  have hd : 0 < sourceDelta X := by unfold sourceDelta; positivity
  have hd1 : sourceDelta X ≤ 1 := by
    unfold sourceDelta
    apply (div_le_one (by positivity)).mpr
    linarith
  have hm := actual_family_right_mean hX hd hd1 (show 0 ≤ X * u / q by positivity)
  have hphi : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have ht : (q.totient : ℝ) ≤ q := Nat.cast_le.mpr (Nat.totient_le q)
  have hb0 : 0 ≤
      2 * (X * u / q) * ((24 / X) * X ^ (-2 * sourceDelta X)) +
      (4 / q) * (3 * (1 + 1 / (2 * sourceDelta X)) ^ 4 +
        (2 / sourceDelta X) * (1 + 1 / ((3 / 2) * sourceDelta X)) ^ 4) +
      (8 / q) * X ^ (-sourceDelta X) * (1 + 1 / sourceDelta X) ^ 5 := by positivity
  have hm' := ((div_le_iff₀ hphi).mp hm).trans (mul_le_mul_of_nonneg_left ht hb0)
  have hi : 1 / sourceDelta X = (3 / 2) * Real.log X := by
    unfold sourceDelta
    field_simp
    norm_num
  have hi2 : 1 / (2 * sourceDelta X) = (3 / 4) * Real.log X := by
    rw [show 1 / (2 * sourceDelta X) = (1 / 2) * (1 / sourceDelta X) by ring, hi]
    ring
  have hi3 : 1 / ((3 / 2) * sourceDelta X) = Real.log X := by
    rw [show 1 / ((3 / 2) * sourceDelta X) = (2 / 3) * (1 / sourceDelta X) by ring, hi]
    ring
  have hi4 : 2 / sourceDelta X = 3 * Real.log X := by
    rw [show 2 / sourceDelta X = 2 * (1 / sourceDelta X) by ring, hi]
    ring
  rw [hi2, hi3, hi4, hi] at hm'
  have he :
      (2 * (X * u / q) * ((24 / X) * X ^ (-2 * sourceDelta X)) +
      (4 / q) * (3 * (1 + (3 / 4) * Real.log X) ^ 4 +
        (3 * Real.log X) * (1 + Real.log X) ^ 4) +
      (8 / q) * X ^ (-sourceDelta X) * (1 + (3 / 2) * Real.log X) ^ 5) * q =
      48 * u * X ^ (-2 * sourceDelta X) +
      4 * (3 * (1 + (3 / 4) * Real.log X) ^ 4 +
        (3 * Real.log X) * (1 + Real.log X) ^ 4) +
      8 * X ^ (-sourceDelta X) * (1 + (3 / 2) * Real.log X) ^ 5 := by
    field_simp
    ring
  rw [he] at hm'
  have hdiag := mul_le_mul_of_nonneg_left (source_shift_decay hX1)
    (show 0 ≤ 48 * u by positivity)
  have hmass := mul_le_mul_of_nonneg_right (source_shift_mass_decay hX1)
    (show 0 ≤ 8 * (1 + (3 / 2) * Real.log X) ^ 5 by positivity)
  have herr := family_right_error_polynomial hL
  have hslope : 24 ≤ 0.0003 * Real.log X ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) hL 5
    norm_num at hp
    linarith
  have hsl := mul_le_mul_of_nonneg_right hslope hu
  have hp : 0 ≤ Real.log X ^ 5 := by positivity
  nlinarith only [hm', hdiag, hmass, herr, hsl, hp]

theorem source_full_nonprincipal_chen14 (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -(y * u)..(y * u),
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y)
        (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2) ≤
      (67.929 + 0.0003 * u) * Real.log ((q : ℝ) * y) ^ 5 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy' := source_height_ge_ten_thousand hy
  have hX : 2 * (q : ℝ) ≤ (q : ℝ) * y := by nlinarith
  have hlarge : 100000 ≤ (q : ℝ) * y := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    nlinarith
  have hlog : 11 ≤ Real.log ((q : ℝ) * y) := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 100000) hlarge
    have hval : 11 ≤ Real.log 100000 := by
      rw [show (100000 : ℝ) = 10 ^ (5 : ℕ) by norm_num, Real.log_pow,
        show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    exact hval.trans ht
  have h := full_nonprincipal_right_mean hX hlog hu
  have he : (q : ℝ) * y * u / q = y * u := by field_simp
  simpa only [he] using h

#print axioms source_full_nonprincipal_chen14

end LiuWang.Proof.Campaign20260915.Density
