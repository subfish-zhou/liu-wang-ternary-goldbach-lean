import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenBoundary
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

/-!
LWD p.288, last two displayed inequalities: combine the principal contribution
with Chen's nonprincipal contribution without losing multiplicities or endpoints.
Neither of the high-alpha analytic inputs is constructed in this file.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

def principalSevenBound (alpha y : ℝ) : ℝ :=
  16541 * (Real.log y) ^ (6 : ℕ) +
    11402 * y ^ (4 * (1 - alpha)) * (Real.log y) ^ (6 * alpha) +
    3872 * y ^ (4 * (1 - alpha)) * (Real.log y) ^ (8 * alpha - 3)

theorem principal_power_le_family {q alpha y : ℝ}
    (hq : 1 ≤ q) (hy : 1 ≤ y) (ha : alpha ≤ 1) :
    y ^ (4 * (1 - alpha)) ≤ (q ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) := by
  have hq3 : 1 ≤ q ^ (3 : ℕ) := one_le_pow₀ hq
  have hbase : y ^ (4 : ℕ) ≤ q ^ (3 : ℕ) * y ^ (4 : ℕ) := by
    nlinarith [pow_nonneg (by linarith : 0 ≤ y) 4]
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num,
    Real.rpow_natCast_mul (by linarith : 0 ≤ y) 4]
  exact Real.rpow_le_rpow (by positivity) hbase (by linarith)

theorem principal_log_powers {L S alpha : ℝ}
    (hL : 1 ≤ L) (hLS : L ≤ S) (ha : 1 / 2 ≤ alpha) (ha1 : alpha ≤ 1) :
    L ^ (6 * alpha) ≤ S ^ (6 * alpha) ∧
      L ^ (8 * alpha - 3) ≤ S ^ (6 * alpha) / S := by
  have hS : 0 < S := by linarith
  constructor
  · exact Real.rpow_le_rpow (by linarith) hLS (by linarith)
  · calc
      L ^ (8 * alpha - 3) ≤ L ^ (6 * alpha - 1) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      _ ≤ S ^ (6 * alpha - 1) :=
        Real.rpow_le_rpow (by linarith) hLS (by linarith)
      _ = _ := by rw [Real.rpow_sub hS, Real.rpow_one]

theorem principal_plus_chen_le_sourceSeven (q : ℕ) [NeZero q]
    {alpha y : ℝ} (hy : 10000 ≤ y) (ha : 1 / 2 ≤ alpha) (ha1 : alpha ≤ 1) :
    principalSevenBound alpha y + chenBound q alpha y ≤
      sourceSevenBound q alpha y := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hy0 : 0 < y := by linarith
  have hL : 1 ≤ Real.log y := (by norm_num : (1 : ℝ) ≤ 8).trans (log_height_ge_eight hy)
  have hLS : Real.log y ≤ Real.log ((q : ℝ) * y) :=
    Real.log_le_log hy0 (by nlinarith)
  have hS : 0 < Real.log ((q : ℝ) * y) := by linarith
  let D := ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha)
  let E := (Real.log ((q : ℝ) * y)) ^ (6 * alpha)
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  have hp := principal_power_le_family hq (by linarith : 1 ≤ y) ha1
  obtain ⟨hlog, hlog'⟩ := principal_log_powers hL hLS ha ha1
  have hmain := mul_le_mul hp hlog (Real.rpow_nonneg (by linarith) _) hD
  have hextra := mul_le_mul hp hlog' (Real.rpow_nonneg (by linarith) _) hD
  have heq :
      16541 * (Real.log y) ^ (6 : ℕ) + 11402 * (D * E) +
        3872 * (D * (E / Real.log ((q : ℝ) * y))) +
        (250359 / Real.log ((q : ℝ) * y) + 5700) * D * E =
          sourceSevenBound q alpha y := by
    unfold sourceSevenBound
    dsimp [D, E]
    ring
  rw [← heq]
  unfold principalSevenBound chenBound
  dsimp [D, E] at *
  nlinarith only [hmain, hextra]

theorem chenBound_nonneg (q : ℕ) [NeZero q] {alpha y : ℝ} (hy : 10000 ≤ y) :
    0 ≤ chenBound q alpha y := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hlog := log_product_ge_eight hq hy
  unfold chenBound
  positivity

theorem family_high_from_original_inputs (q : ℕ) [NeZero q]
    {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 < alpha) (ha1 : alpha < 1)
    (hprincipal : (count (1 : Character 1) alpha y : ℝ) ≤ principalSevenBound alpha y)
    (hchen : 3 ≤ q → ∀ beta ∈ Ico (1 / 2) 1,
      (strictNonprincipalCount q beta y : ℝ) ≤ chenBound q beta y) :
    (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y := by
  have hy' := source_height_ge_ten_thousand hy
  have hnon : (nonprincipalCount q alpha y : ℝ) ≤ chenBound q alpha y := by
    by_cases hq : 3 ≤ q
    · exact closed_nonprincipal_of_chen q (by linarith) ha ha1 (hchen hq)
    · have hsmall : q = 1 ∨ q = 2 := by have := NeZero.pos q; omega
      rcases hsmall with rfl | rfl <;>
        simpa only [nonprincipalCount_one, nonprincipalCount_two, Nat.cast_zero] using
          (chenBound_nonneg _ hy' (alpha := alpha))
  rw [familyCount_split, Nat.cast_add]
  exact (add_le_add hprincipal hnon).trans
    (principal_plus_chen_le_sourceSeven q hy' ha.le ha1.le)

theorem family_sourceSeven_from_original_inputs (q : ℕ) [NeZero q]
    {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1)
    (hprincipal : 1 / 2 + 2 * sourceDelta y ≤ alpha →
      (count (1 : Character 1) alpha y : ℝ) ≤ principalSevenBound alpha y)
    (hchen : 3 ≤ q → ∀ beta ∈ Ico (1 / 2) 1,
      (strictNonprincipalCount q beta y : ℝ) ≤ chenBound q beta y) :
    (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y := by
  by_cases hlow : alpha ≤ 1 / 2 + 2 * sourceDelta y
  · exact familyCount_le_sourceSeven_original_low q hy ha hlow
  · have hy' := source_height_ge_ten_thousand hy
    have hlog := log_height_ge_eight hy'
    have hd : 0 < sourceDelta y := by unfold sourceDelta; positivity
    exact family_high_from_original_inputs q hy (by linarith) ha1
      (hprincipal (le_of_not_ge hlow)) hchen

theorem complete_family_sourceSeven_from_original_inputs (q : ℕ) [NeZero q]
    {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1)
    (hprincipal : 1 / 2 + 2 * sourceDelta y ≤ alpha →
      (count (1 : Character 1) alpha y : ℝ) ≤ principalSevenBound alpha y)
    (hchen : 3 ≤ q → ∀ beta ∈ Ico (1 / 2) 1,
      (strictNonprincipalCount q beta y : ℝ) ≤ chenBound q beta y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      16541 * (Real.log y) ^ (6 : ℕ) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
          (Real.log ((q : ℝ) * y)) ^ (6 * alpha) := by
  simpa only [familyCount_eq_complete_filter q ha, Nat.cast_sum, sourceSevenBound] using
    family_sourceSeven_from_original_inputs q hy ha ha1 hprincipal hchen

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
