import LiuWang.Proof.Campaign20260915.Density.ChenConstants

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Set
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis (cosineDetector)
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

def chenInterpolatedBound (q : ℕ) (y sigma : ℝ) : ℝ :=
  42.6154 * (30.5879 : ℝ) ^ sigma *
    (((q : ℝ) * y) ^ (3 : ℕ) * y) ^ (1 - sigma) *
    Real.log ((q : ℝ) * y) ^ (6 * sigma - 1)

theorem chen_endpoint_scalar (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    chenEndpointBudget q y sigma ≤ chenInterpolatedBound q y sigma := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  let A : ℝ := 235.69 * X ^ (3 / 2 : ℝ) * y ^ (1 / 2 : ℝ) * L ^ 2
  let B : ℝ := 90.5727 * L ^ 5
  let theta : ℝ := (sigma - 1 / 2) / (1 / 2 + sourceDelta X)
  let R : ℝ := 42.6154 * (30.5879 : ℝ) ^ sigma *
    (X ^ (3 : ℕ) * y) ^ (1 - sigma) * L ^ (6 * sigma - 1)
  let K : ℝ := Real.log 42.6154 + 3 * L + Real.log y - Real.log L
  let H : ℝ := Real.log 30.5879 - (3 * L + Real.log y) + 6 * Real.log L
  have hy0 : 0 < y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX0 : 0 < X := by dsimp [X]; positivity
  have hyX : y ≤ X := by dsimp [X]; nlinarith
  have hL : 11 ≤ L := source_product_log_ge_eleven q hy
  have hL0 : 0 < L := by linarith
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hlogy : Real.log y ≤ L := Real.log_le_log hy0 hyX
  have hla : Real.log A = Real.log 235.69 + (3 / 2) * L +
      (1 / 2) * Real.log y + 2 * Real.log L := by
    dsimp only [A]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hX0, Real.log_rpow hy0, Real.log_pow]
    rfl
  have hlb : Real.log B = Real.log 90.5727 + 5 * Real.log L := by
    dsimp only [B]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  have hd : 0 ≤ sourceDelta X := (source_product_shift_bounds q hy).1.le
  have hdL : sourceDelta X * L = 2 / 3 := by
    unfold sourceDelta
    change 1 / (1.5 * L) * L = _
    field_simp
    norm_num
  have hleft : Real.log A ≤ K + (1 / 2) * H := by
    rw [hla]
    dsimp only [K, H]
    linarith only [chen_log_left_constant]
  have hright : Real.log B ≤ K + (1 + sourceDelta X) * H := by
    have hgap := mul_le_mul_of_nonneg_left
      (show 3 * L + Real.log y ≤ 4 * L by linarith) hd
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have hlogC : 0 ≤ Real.log 30.5879 := Real.log_nonneg (by norm_num)
    have hplus := mul_nonneg hd (show 0 ≤ Real.log 30.5879 + 6 * Real.log L by positivity)
    rw [hlb]
    dsimp only [K, H]
    nlinarith only [chen_log_right_constant, hgap, hplus, hdL]
  have hlr : Real.log R = K + sigma * H := by
    dsimp only [R]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow (by norm_num), Real.log_rpow (by positivity), Real.log_rpow hL0,
      Real.log_mul (by positivity) hy0.ne', Real.log_pow]
    dsimp only [K, H, L]
    ring
  change A ^ (1 - theta) * B ^ theta ≤ R
  apply (Real.log_le_log_iff (by positivity) hR0).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA0, Real.log_rpow hB0, hlr]
  exact chen_affine_endpoint_transport hd hs.1 hs.2 hleft hright

theorem source_family_equation_32 (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      chenInterpolatedBound q y sigma := by
  exact (source_family_chen_endpoints q hy hs).trans
    (chen_endpoint_scalar q hy hs)

theorem source_familyMean_equation_32 (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    SourceRoute.Density.Restart.familyMean q ((q : ℝ) * y) sigma y ≤
      1.272 * chenInterpolatedBound q y sigma := by
  exact (source_familyMean_chen_endpoints q hy hs).trans
    (mul_le_mul_of_nonneg_left (chen_endpoint_scalar q hy hs) (by norm_num))

#print axioms source_family_equation_32
#print axioms source_familyMean_equation_32

end LiuWang.Proof.Campaign20260915.Density
