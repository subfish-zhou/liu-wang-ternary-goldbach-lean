import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.OrdinaryBudget

set_option autoImplicit false

noncomputable section

open Classical
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem ordinary_modulus_power_le (q : ℕ) [NeZero q] {y α : ℝ}
    (hy : 10000 ≤ y) (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1) :
    y ^ (4 * (1 - α)) * Real.log y ^ (6 * α) ≤
      ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - α) *
        Real.log ((q : ℝ) * y) ^ (6 * α) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hL := log_ge_nine hy
  have hqp : (1 : ℝ) ≤ (q : ℝ) ^ (3 : ℕ) := one_le_pow₀ hq
  have hbase : y ^ (4 : ℕ) ≤ (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hqp (by positivity : 0 ≤ y ^ (4 : ℕ))
  have hp : y ^ (4 * (1 - α)) ≤ ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - α) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast_mul (by linarith : 0 ≤ y)]
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hyqy : y ≤ (q : ℝ) * y := by nlinarith
  have hlog := Real.log_le_log (by linarith : 0 < y) hyqy
  have hlp := Real.rpow_le_rpow (by linarith : 0 ≤ Real.log y) hlog
    (show 0 ≤ 6 * α by linarith)
  exact mul_le_mul hp hlp (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _)

theorem ordinary_budget_le_sourceSeven (q : ℕ) [NeZero q] {y α : ℝ}
    (hy : 10000 ≤ y) (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1) :
    7000 * y ^ (4 * (1 - α)) * Real.log y ^ (6 * α) + 51 * Real.log y ^ 3 ≤
      sourceSevenBound q α y := by
  have hL := log_ge_nine hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlog := log_product_ge_eight hq hy
  have hp := ordinary_modulus_power_le q hy hα hα1
  have hcoef : (7000 : ℝ) ≤ 17102 + 254231 / Real.log ((q : ℝ) * y) := by
    have h : 0 ≤ 254231 / Real.log ((q : ℝ) * y) := by positivity
    linarith
  have hmain := mul_le_mul hcoef hp
    (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ y) _) (Real.rpow_nonneg (by linarith) _))
    (by positivity)
  have hlp : Real.log y ^ 3 ≤ Real.log y ^ 6 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsmall : 51 * Real.log y ^ 3 ≤ 16541 * Real.log y ^ 6 := by
    nlinarith [show 0 ≤ Real.log y ^ 6 by positivity]
  unfold sourceSevenBound
  nlinarith only [hmain, hsmall]

theorem ordinary_low_high_cover {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 ≤ α) (hα1 : α < 1) :
    (1 / 2 ≤ α ∧ α ≤ 2 / 3) ∨ (1 / 2 + 2 * delta y ≤ α ∧ α < 1) := by
  have hd := (delta_bounds hy).2
  by_cases hlow : α ≤ 2 / 3
  · exact Or.inl ⟨hα, hlow⟩
  · exact Or.inr ⟨by linarith, hα1⟩

theorem ordinary_principal_le_family (q : ℕ) [NeZero q] (α y : ℝ) :
    count (1 : Character q) α y ≤ familyCount q α y := by
  exact Finset.single_le_sum (f := fun χ : Character q => count χ α y)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (1 : Character q))

theorem ordinary_principal_sourceSeven (q : ℕ) [NeZero q] {y α : ℝ}
    (hy : 10000 ≤ y) (hα : 1 / 2 ≤ α) (hα1 : α < 1) :
    (count (1 : Character q) α y : ℝ) ≤ sourceSevenBound q α y := by
  rcases ordinary_low_high_cover hy hα hα1 with hlow | hhigh
  · have h := ordinary_principal_le_family q α y
    have hr : (count (1 : Character q) α y : ℝ) ≤ (familyCount q α y : ℝ) := by exact_mod_cast h
    exact hr.trans (familyCount_le_sourceSeven_low q hy hlow.1 hlow.2)
  · exact (ordinary_principal_budget q hy hhigh.1 hhigh.2).trans
      (ordinary_budget_le_sourceSeven q hy hα hα1.le)

theorem ordinary_complete_principal_sourceSeven (q : ℕ) [NeZero q] {y α : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hα : 1 / 2 ≤ α) (hα1 : α < 1) :
    (∑ s ∈ (CompleteExpansion.zeroValues (1 : Character q) y).filter
      (fun s => α ≤ s.re), (analyticOrderNatAt (1 : Character q).LFunction s : ℝ)) ≤
      sourceSevenBound q α y := by
  have h := ordinary_principal_sourceSeven q (source_height_ge_ten_thousand hy) hα hα1
  simpa only [count, values_eq_complete_filter _ hα, Nat.cast_sum] using h

theorem ordinary_family_split (q : ℕ) [NeZero q] (α y : ℝ) :
    familyCount q α y = count (1 : Character q) α y +
      ∑ χ ∈ (Finset.univ : Finset (Character q)).erase 1, count χ α y := by
  classical
  unfold familyCount
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q))]
  omega

theorem ordinary_family_principal_paid (q : ℕ) [NeZero q] {y α : ℝ}
    (hy : 10000 ≤ y) (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (familyCount q α y : ℝ) ≤
      7000 * y ^ (4 * (1 - α)) * Real.log y ^ (6 * α - 6 * delta y) + 51 * Real.log y ^ 3 +
        ∑ χ ∈ (Finset.univ : Finset (Character q)).erase 1, (count χ α y : ℝ) := by
  rw [ordinary_family_split, Nat.cast_add, Nat.cast_sum]
  exact add_le_add_left (ordinary_principal_budget_sharp q hy hα hα1) _

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
