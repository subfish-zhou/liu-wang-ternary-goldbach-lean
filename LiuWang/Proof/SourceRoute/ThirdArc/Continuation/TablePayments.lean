import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.TableIntegrals

/-! Full-family 14000/20/13 payments on the original moving beta subintervals. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

def threeRowPrice (X z d : ℝ) : ℝ :=
  14000 * (Real.exp (-0.36 * Real.log X / Real.log z) -
    Real.exp (-0.478 * Real.log X / Real.log z)) +
  20 * (Real.exp (-0.33 * Real.log X / Real.log z) -
    Real.exp (-0.36 * Real.log X / Real.log z)) +
  13 * (Real.exp (-d * Real.log X / Real.log z) -
    Real.exp (-0.33 * Real.log X / Real.log z))

theorem M3_three_row_integral_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y d : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y) (hd : 0 ≤ d) (hd33 : d ≤ 0.33) :
    countIntegral q X y (1 - 0.478 / Real.log ((q : ℝ) * y))
        (1 - d / Real.log ((q : ℝ) * y)) ≤ threeRowPrice X ((q : ℝ) * y) d := by
  have hl : 0 ≤ Real.log ((q : ℝ) * y) := (by norm_num : (0 : ℝ) ≤ 30).trans
    (M3_log_product_ge_thirty hN hq hy)
  have h48_36 : 1 - 0.478 / Real.log ((q : ℝ) * y) ≤
      1 - 0.36 / Real.log ((q : ℝ) * y) :=
    sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hl) 1
  have h36_33 : 1 - 0.36 / Real.log ((q : ℝ) * y) ≤
      1 - 0.33 / Real.log ((q : ℝ) * y) :=
    sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hl) 1
  have h33_d : 1 - 0.33 / Real.log ((q : ℝ) * y) ≤
      1 - d / Real.log ((q : ℝ) * y) :=
    sub_le_sub_left (div_le_div_of_nonneg_right hd33 hl) 1
  have hx : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hh := rowCutoff_ge_half .r0478 (M3_table_domain hN hq hy).1
  change 1 / 2 ≤ 1 - 0.478 / Real.log ((q : ℝ) * y) at hh
  rw [countIntegral_split q y hx hh h48_36 (h36_33.trans h33_d),
    countIntegral_split q y hx (hh.trans h48_36) h36_33 h33_d]
  have h48 := M3_near_one_integral_paid .r0478 hN hq hX hy (d := 0.36)
    (by norm_num) (by norm_num [rowLambda])
  have h36 := M3_near_one_integral_paid .r036 hN hq hX hy (d := 0.33)
    (by norm_num) (by norm_num [rowLambda])
  have h33 := M3_near_one_integral_paid .r033 hN hq hX hy hd hd33
  have h := add_le_add h48 (add_le_add h36 h33)
  norm_num only [rowCutoff, rowLambda, rowBound, rowMultiplicity, rowSelectedBound,
    Nat.cast_mul, Nat.cast_ofNat, threeRowPrice] at h ⊢
  linarith

theorem M3_countIntegral_split_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y) :
    countIntegral q X y (59 / 60) 1 ≤
      countIntegral q X y (59 / 60) (1 - 0.478 / Real.log ((q : ℝ) * y)) +
        threeRowPrice X ((q : ℝ) * y) 0 := by
  have hcut := M3_rowCutoff_ge_source_split .r0478 hN hq hy
  have htop := rowCutoff_le_one .r0478 (M3_table_domain hN hq hy).1
  rw [countIntegral_split q y (lt_of_lt_of_le zero_lt_one hX) (by norm_num) hcut htop]
  apply add_le_add le_rfl
  have h := M3_three_row_integral_paid hN hq hX hy (d := 0) (by norm_num) (by norm_num)
  norm_num only [rowCutoff, rowLambda, zero_div, sub_zero] at h ⊢
  exact h

theorem M3_low_three_row_integral_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    (∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * lowHeight))..
        (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)),
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      lowCoefficient (59 / 60) * threeRowPrice N ((q : ℝ) * lowHeight) 0.2067 := by
  have hx := natCast_pos_of_exp_le hN
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hl : 0 ≤ Real.log ((q : ℝ) * lowHeight) := (by norm_num : (0 : ℝ) ≤ 30).trans
    (M3_log_product_ge_thirty hN hq le_rfl)
  have hab : 1 - 0.478 / Real.log ((q : ℝ) * lowHeight) ≤
      1 - 0.2067 / Real.log ((q : ℝ) * lowHeight) :=
    sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hl) 1
  have hcut := M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl
  have hh : 1 / 2 ≤ 1 - 0.478 / Real.log ((q : ℝ) * lowHeight) :=
    (by norm_num : (1 : ℝ) / 2 ≤ 59 / 60).trans hcut
  calc
    _ ≤ ∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * lowHeight))..
        (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)),
        lowCoefficient (59 / 60) * (betaKernel N alpha * familyCount q alpha lowHeight) := by
      apply intervalIntegral.integral_mono_on hab (family_low_integrable q _ hx hh hab)
        ((family_beta_integrable q _ hx hh hab).const_mul _)
      intro alpha halpha
      have h := mul_le_mul_of_nonneg_right
        (lowCoefficient_antitone (by norm_num : (0 : ℝ) < 59 / 60)
          (hcut.trans halpha.1))
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le (alpha - 1)) (Real.log_nonneg hX))
          (Nat.cast_nonneg (familyCount q alpha lowHeight)))
      exact (show betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight =
        lowCoefficient alpha * (betaKernel N alpha * familyCount q alpha lowHeight) by ring).trans_le h
    _ = _ := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (M3_three_row_integral_paid hN hq hX le_rfl (by norm_num) (by norm_num))
      (lowCoefficient_nonneg (by norm_num))

theorem original_middle_base_ge_one {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 ≤ 0.001 * (N : ℝ) := by
  have h := (Real.add_one_le_exp (3100 : ℝ)).trans hN
  linarith

theorem original_middle_endpoint_split_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1 ≤
      countIntegral q (0.001 * N) (middleHeight N q) (59 / 60)
        (1 - 0.478 / Real.log ((q : ℝ) * middleHeight N q)) +
      threeRowPrice (0.001 * N) ((q : ℝ) * middleHeight N q) 0 := by
  have hn : Real.exp 2000 ≤ (N : ℝ) := (Real.exp_le_exp.mpr (by norm_num)).trans hN
  exact M3_countIntegral_split_paid hN hq (original_middle_base_ge_one hN)
    (original_height_order hn hq1).1

theorem original_high_endpoint_split_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    countIntegral q N (sourceT N) (59 / 60) 1 ≤
      countIntegral q N (sourceT N) (59 / 60)
        (1 - 0.478 / Real.log ((q : ℝ) * sourceT N)) +
      threeRowPrice N ((q : ℝ) * sourceT N) 0 := by
  have hn : Real.exp 2000 ≤ (N : ℝ) := (Real.exp_le_exp.mpr (by norm_num)).trans hN
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  exact M3_countIntegral_split_paid hN hq hX
    ((original_height_order hn hq1).1.trans (original_height_order hn hq1).2)

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
