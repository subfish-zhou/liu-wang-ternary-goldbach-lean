import LiuWang.Proof.Campaign20260915.Density.CompleteMollifier

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Classical
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_product_log_ge_eleven (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    11 ≤ Real.log ((q : ℝ) * y) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlarge : 100000 ≤ (q : ℝ) * y := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    nlinarith only [h]
  have hval : 11 ≤ Real.log 100000 := by
    rw [show (100000 : ℝ) = 10 ^ (5 : ℕ) by norm_num, Real.log_pow,
      show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  exact hval.trans (Real.log_le_log (by norm_num) hlarge)

theorem complete_chen24_scalar {a b u : ℝ} (ha : 0 ≤ a) (hL : 11 ≤ a + b) (hu : 0 ≤ u) :
    2 * u * (a + b + 0.7) + 2.5 * b + 4.2 ≤
      (2.19021 * u + 2.906) * (a + b) - (24 / Real.pi ^ 2) * a := by
  have hp : 24 / Real.pi ^ 2 ≤ 2.5 := by
    calc
      _ = 4 * (6 / Real.pi ^ 2) := by ring
      _ ≤ 4 * 0.608 := mul_le_mul_of_nonneg_left euler_density_bounds.2 (by norm_num)
      _ ≤ _ := by norm_num
  have hpa := mul_le_mul_of_nonneg_right hp ha
  have hprod := mul_nonneg hu (show 0 ≤ 0.19021 * (a + b) - 1.4 by linarith)
  nlinarith only [hpa, hprod, hL]

theorem complete_family_chen24 (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    (∑ chi : Character q, ∫ t in -(y * u)..y * u,
      ‖NonprincipalDensityAdvance.Q chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      (q.totient : ℝ) * y *
        ((2.19021 * u + 2.906) * Real.log ((q : ℝ) * y) - (24 / Real.pi ^ 2) * Real.log q) := by
  have hy0 : 0 < y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hlog : Real.log ((q : ℝ) * y) = Real.log q + Real.log y :=
    Real.log_mul hq0.ne' hy0.ne'
  have hL := source_product_log_ge_eleven q hy
  rw [hlog] at hL
  have hs := complete_chen24_scalar (Real.log_nonneg hq) hL hu
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (q.totient : ℝ) * y by positivity)
  rw [← hlog] at hm
  exact (complete_Q_mean_prebudget q hy hu).trans hm

theorem nonprincipal_Q_mean_chen24 (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -(y * u)..y * u,
      ‖NonprincipalDensityAdvance.Q chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      (q.totient : ℝ) * y *
        ((2.19021 * u + 2.906) * Real.log ((q : ℝ) * y) - (24 / Real.pi ^ 2) * Real.log q) := by
  have hy0 : 0 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  apply (sum_le_sum_of_subset_of_nonneg (erase_subset (1 : Character q) univ)
    (fun chi _ _ => intervalIntegral.integral_nonneg (by nlinarith : -(y * u) ≤ y * u)
      (fun _ _ => sq_nonneg _))).trans (complete_family_chen24 q hy hu)

#print axioms complete_family_chen24
#print axioms nonprincipal_Q_mean_chen24

end LiuWang.Proof.Campaign20260915.Density
