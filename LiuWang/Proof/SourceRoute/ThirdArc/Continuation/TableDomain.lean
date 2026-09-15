import LiuWang.Proof.SourceRoute.ThirdArc.BetaIntegrals
import LiuWang.Proof.NearOneDensity.Continuation.CountInterface

/-! The admitted table's effective domain on every original M3 height window. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

def rowCutoff (r : DensityRow) (z : ℝ) : ℝ := 1 - rowLambda r / Real.log z

theorem lowHeight_ge_one : (1 : ℝ) ≤ lowHeight := by
  unfold lowHeight
  linarith [Real.pi_gt_three]

theorem M3_modulus_large {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    (3100 : ℝ) ^ 3 ≤ q :=
  (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 3).trans hq

theorem M3_table_domain {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y : ℝ} (hy : lowHeight ≤ y) :
    100000000000 ≤ (q : ℝ) * y ∧ (q : ℝ) * max 1 y ≤ (q : ℝ) * y := by
  have hqbig := M3_modulus_large hN hq
  have hybig : 30000 ≤ y := by
    have hpi := Real.pi_gt_three
    unfold lowHeight at hy
    nlinarith
  refine ⟨?_, ?_⟩
  · have h := mul_le_mul hqbig hybig (by norm_num) (Nat.cast_nonneg (α := ℝ) q)
    norm_num at h
    linarith
  · rw [max_eq_right (lowHeight_ge_one.trans hy)]

theorem low_table_domain {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    100000000000 ≤ (q : ℝ) * lowHeight ∧
      (q : ℝ) * max 1 lowHeight ≤ (q : ℝ) * lowHeight :=
  M3_table_domain hN hq le_rfl

theorem M3_log_product_ge_thirty {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y : ℝ} (hy : lowHeight ≤ y) :
    30 ≤ Real.log ((q : ℝ) * y) := by
  have hz := (M3_table_domain hN hq hy).1
  have hybig : 30000 ≤ y := by
    unfold lowHeight at hy
    nlinarith [Real.pi_gt_three]
  have hprod := mul_le_mul (M3_modulus_large hN hq) hybig (by norm_num)
    (Nat.cast_nonneg (α := ℝ) q)
  apply (Real.le_log_iff_exp_le (by linarith : 0 < (q : ℝ) * y)).mpr
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 30
  rw [← Real.exp_nat_mul] at he
  norm_num at he hprod
  linarith

theorem middle_table_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq0 : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    100000000000 ≤ (q : ℝ) * middleHeight N q ∧
      (q : ℝ) * max 1 (middleHeight N q) ≤ (q : ℝ) * middleHeight N q :=
  M3_table_domain hN hq0 (original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).1

theorem high_table_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq0 : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    100000000000 ≤ (q : ℝ) * sourceT N ∧
      (q : ℝ) * max 1 (sourceT N) ≤ (q : ℝ) * sourceT N := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  exact M3_table_domain hN hq0 (hh.1.trans hh.2)

theorem M3_familyCount_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {alpha y : ℝ} (hy : lowHeight ≤ y) (ha : rowCutoff r ((q : ℝ) * y) ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ rowBound r :=
  NearOneDensity.Continuation.familyCount_row_tail r
    (M3_table_domain hN hq hy).1 (M3_table_domain hN hq hy).2 ha

theorem M3_familyCount_14000 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {alpha y : ℝ} (hy : lowHeight ≤ y)
    (ha : 1 - 0.478 / Real.log ((q : ℝ) * y) ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ 14000 := by
  simpa only [rowBound, rowMultiplicity, rowSelectedBound] using
    M3_familyCount_row .r0478 hN hq hy ha

theorem M3_familyCount_13 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {alpha y : ℝ} (hy : lowHeight ≤ y)
    (ha : 1 - 0.33 / Real.log ((q : ℝ) * y) ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ 13 := by
  simpa only [rowBound, rowMultiplicity, rowSelectedBound] using
    M3_familyCount_row .r033 hN hq hy ha

theorem M3_familyCount_20 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {alpha y : ℝ} (hy : lowHeight ≤ y)
    (ha : 1 - 0.36 / Real.log ((q : ℝ) * y) ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ 20 := by
  simpa only [rowBound, rowMultiplicity, rowSelectedBound] using
    M3_familyCount_row .r036 hN hq hy ha

theorem rowCutoff_ge_half (r : DensityRow) {z : ℝ} (hz : 100000000000 ≤ z) :
    1 / 2 ≤ rowCutoff r z :=
  NearOneDensity.source_alpha_ge_half hz (row_basic_certificate r).2.1

theorem rowCutoff_le_one (r : DensityRow) {z : ℝ} (hz : 100000000000 ≤ z) :
    rowCutoff r z ≤ 1 := by
  have hl : 0 ≤ rowLambda r := by cases r <;> norm_num [rowLambda]
  have hz1 : 1 ≤ z := by linarith
  exact sub_le_self _ (div_nonneg hl (Real.log_nonneg hz1))

theorem M3_rowCutoff_ge_source_split (r : DensityRow) {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y : ℝ} (hy : lowHeight ≤ y) :
    59 / 60 ≤ rowCutoff r ((q : ℝ) * y) := by
  have hl := M3_log_product_ge_thirty hN hq hy
  have hr := (row_basic_certificate r).2.1
  have h : rowLambda r / Real.log ((q : ℝ) * y) ≤ 1 / 60 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  unfold rowCutoff
  linarith

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
