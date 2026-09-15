import LiuWang.Proof.Campaign20260915.Density.PrincipalSeven
import LiuWang.Proof.Campaign20260915.Density.DensityScale

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem strict_nonprincipal_le_closed (q : ℕ) [NeZero q] (alpha y : ℝ) :
    strictNonprincipalCount q alpha y ≤ nonprincipalCount q alpha y := by
  unfold strictNonprincipalCount nonprincipalCount count
  apply sum_le_sum
  intro chi _
  apply sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    obtain ⟨hz, h0, h1, ht, ha⟩ := (mem_strict_values chi).mp hrho
    exact mem_zeroValues.mpr ⟨hz, ⟨h0, h1, ht⟩, ha.le⟩
  · intros
    exact Nat.zero_le _

theorem closed_nonprincipal_chen_low (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha' : alpha ≤ 2 / 3) :
    (nonprincipalCount q alpha y : ℝ) ≤ chenBound q alpha y := by
  have hy' := source_height_ge_ten_thousand hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hL := source_product_log_ge_eleven q hy
  have hpow := density_power_ge_product hq (by linarith : 1 ≤ y) ha'
  have hlogpow : Real.log ((q : ℝ) * y) ≤
      Real.log ((q : ℝ) * y) ^ (6 * alpha) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ Real.log ((q : ℝ) * y)) (by linarith : 1 ≤ 6 * alpha)
  have hscale : (q : ℝ) * y * Real.log ((q : ℝ) * y) ≤ chenDensityScale q y alpha :=
    mul_le_mul hpow hlogpow (by linarith) (by positivity)
  have hsub : nonprincipalCount q alpha y ≤ familyCount q alpha y := by
    rw [familyCount_split]
    omega
  have hcount := (Nat.cast_le.mpr hsub).trans (familyCount_le_ten q alpha hy')
  have hpos := (source_density_scale_pos q hy alpha).le
  have hcoeff : 0 ≤ 250359 / Real.log ((q : ℝ) * y) := by positivity
  have hc := mul_nonneg hcoeff hpos
  have he : chenBound q alpha y =
      (250359 / Real.log ((q : ℝ) * y) + 5700) * chenDensityScale q y alpha := by
    unfold chenBound chenDensityScale
    ring
  rw [he]
  nlinarith only [hcount, hscale, hc, hpos]

end LiuWang.Proof.Campaign20260915.Density
