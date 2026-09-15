import LiuWang.Proof.Campaign20260915.Density.PointInterpolation
import LiuWang.Proof.Campaign20260915.Density.ChenConstants

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

def chenPointScale (q : ℕ) (y : ℝ) : ℝ :=
  Real.sqrt q * ((q : ℝ) * y) * y * Real.log q

def chenPointBound (q : ℕ) (y sigma : ℝ) : ℝ :=
  37.102 * chenPointScale q y ^ (2 * (1 - sigma)) *
    Real.log ((q : ℝ) * y) ^ (8 * sigma - 4)

theorem chen_point_scale_log_upper (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y : ℝ} (hy : 0 < y) :
    Real.log (chenPointScale q y) ≤ 2 * Real.log ((q : ℝ) * y) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) < q := Nat.one_lt_cast.mpr (by omega)
  have hlog : 0 < Real.log q := Real.log_pos hq1
  have hh := Real.log_le_sub_one_of_pos (show 0 < Real.log q / 2 by positivity)
  rw [Real.log_div hlog.ne' (by norm_num)] at hh
  have hc : Real.log (Real.log q) ≤ Real.log q / 2 := by
    linarith [Real.log_two_lt_d9]
  unfold chenPointScale
  rw [Real.log_mul (by positivity) hlog.ne',
    Real.log_mul (by positivity) hy.ne',
    Real.log_mul (Real.sqrt_ne_zero'.mpr hq0) (by positivity),
    Real.log_sqrt hq0.le, Real.log_mul hq0.ne' hy.ne']
  linarith

theorem chen_point_endpoint_scalar (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    let theta := (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))
    (37.1 * chenPointScale q y) ^ (1 - theta) *
      (2 * Real.log ((q : ℝ) * y) ^ 4) ^ theta ≤ chenPointBound q y sigma := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  let D : ℝ := chenPointScale q y
  let A : ℝ := 37.1 * D
  let B : ℝ := 2 * L ^ 4
  let K : ℝ := Real.log 37.102 + 2 * Real.log D - 4 * Real.log L
  let H : ℝ := -2 * Real.log D + 8 * Real.log L
  have hy0 : 0 < y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlq : 0 < Real.log q := Real.log_pos (Nat.one_lt_cast.mpr (by omega : 1 < q))
  have hD0 : 0 < D := by dsimp [D, chenPointScale]; positivity
  have hL : 11 ≤ L := source_product_log_ge_eleven q hy
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hd := (source_product_shift_bounds q hy).1.le
  have hdL : sourceDelta X * L = 2 / 3 := by
    unfold sourceDelta
    change 1 / (1.5 * L) * L = _
    field_simp
    norm_num
  have hla : Real.log A = Real.log 37.1 + Real.log D :=
    Real.log_mul (by norm_num) hD0.ne'
  have hlb : Real.log B = Real.log 2 + 4 * Real.log L := by
    dsimp [B]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  have hc : Real.log 2 + 8 / 3 ≤ Real.log 37.102 := by
    have he : 2 * Real.exp (8 / 3) ≤ (37.102 : ℝ) := by
      linarith only [chen_exp_eight_thirds]
    have h := Real.log_le_log (show 0 < 2 * Real.exp (8 / 3) by positivity) he
    rwa [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h
  have hleft : Real.log A ≤ K + (1 / 2) * H := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 37.1)
      (by norm_num : (37.1 : ℝ) ≤ 37.102)
    rw [hla]
    dsimp [K, H]
    linarith only [h]
  have hright : Real.log B ≤ K + (1 + sourceDelta X) * H := by
    have hm := mul_le_mul_of_nonneg_left (chen_point_scale_log_upper q hq hy0) hd
    have hp := mul_nonneg hd hlogL
    rw [hlb]
    dsimp only [K, H]
    change sourceDelta X * Real.log D ≤ sourceDelta X * (2 * L) at hm
    nlinarith only [hc, hm, hp, hdL]
  have hlr : Real.log (chenPointBound q y sigma) = K + sigma * H := by
    unfold chenPointBound
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hD0, Real.log_rpow hL0]
    dsimp only [K, H, D, L, X]
    ring
  apply (Real.log_le_log_iff (by positivity) (by unfold chenPointBound; positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA0,
    Real.log_rpow hB0, hlr]
  exact chen_affine_endpoint_transport hd hs.1 hs.2 hleft hright

theorem source_family_point_equation_18 (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y : ℝ} {s : ℂ} (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : s.re ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    (∑ chi ∈ nonprincipalCharacters q,
      ‖cosineDetector chi ((q : ℝ) * y) y s‖ ^ 2) ≤ chenPointBound q y s.re := by
  apply (source_family_point_interpolation q hq hy hs).trans
  simpa only [chenPointScale, mul_assoc] using chen_point_endpoint_scalar q hq hy hs

end LiuWang.Proof.Campaign20260915.Density
