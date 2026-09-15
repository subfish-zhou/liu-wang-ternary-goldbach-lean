import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Counts

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem countSegment_add {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a b d : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ 0.478) :
    lambdaCountSegment N q y a d =
      lambdaCountSegment N q y a b + lambdaCountSegment N q y b d := by
  have h1 := lambdaCountIntegrand_integrable hN hy ha hab (hbd.trans hd)
  have h2 := lambdaCountIntegrand_integrable hN hy (ha.trans hab) hbd hd
  unfold lambdaCountSegment
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

theorem countSegment_le_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a b C : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 0.478)
    (hc : ∀ lam ∈ Set.Icc a b,
      (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ) ≤ C) :
    lambdaCountSegment N q y a b ≤
      C * lambdaSegment (sourceL N) (Real.log ((q : ℝ) * y)) a b := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.mpr hn
  have hn0' : (N : ℝ) ≠ 0 := hn0.ne'
  have hi : IntervalIntegrable
      (fun lam => C * (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y))) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh := intervalIntegral.integral_mono_on hab
    (lambdaCountIntegrand_integrable hN hy ha hab hb) hi (fun lam hlam => by
      unfold lambdaCountIntegrand
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hc lam hlam)
        (Real.rpow_nonneg hn0.le _))
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 ≤ Real.log ((q : ℝ) * y) := by linarith [original_log_product_ge_ten hN hy]
  have hm := mul_le_mul_of_nonneg_left hh (div_nonneg hL hs)
  rw [intervalIntegral.integral_const_mul] at hm
  rw [lambdaSegment_eq_source_power hn]
  exact hm.trans_eq (by ring)

theorem actual_source35_slice {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hc : FirstCase q y) :
    lambdaCountSegment N q y (1 / c1) 0.36 ≤
      profile35 (sourceL N) (Real.log ((q : ℝ) * y)) := by
  have ha := c1_bounds
  have h1 := countSegment_le_cap hN hy ha.1.le
    (show 1 / c1 ≤ 0.3221 by linarith) (by norm_num : (0.3221 : ℝ) ≤ 0.478)
    (C := 2) (fun lam hlam => by exact_mod_cast actual_first_count hN hq hy hc hlam.2)
  have h2 := lambdaCountSegment_le_row .r033 hN hq hy (a := 0.3221) (b := 0.33)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h3 := lambdaCountSegment_le_row .r036 hN hq hy (a := 0.33) (b := 0.36)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  norm_num [rowBound, rowMultiplicity, rowSelectedBound] at h2 h3
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 < Real.log ((q : ℝ) * y) := by linarith [original_log_product_ge_ten hN hy]
  rw [countSegment_add hN hy ha.1.le (show 1 / c1 ≤ 0.3221 by linarith)
      (by norm_num : (0.3221 : ℝ) ≤ 0.36) (by norm_num),
    countSegment_add hN hy (by norm_num : (0 : ℝ) ≤ 0.3221)
      (by norm_num : (0.3221 : ℝ) ≤ 0.33) (by norm_num) (by norm_num),
    profile35_segments hL hs]
  linarith

theorem second_lower_segment_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hc : SecondCase q y) :
    lambdaCountSegment N q y (1 / c1) 0.12 = 0 := by
  unfold lambdaCountSegment
  have he : (∫ lam in (1 / c1)..(0.12 : ℝ), lambdaCountIntegrand N q y lam) = 0 := by
    calc
      _ = ∫ _lam in (1 / c1)..(0.12 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro lam hlam
        rw [Set.uIcc_of_le c1_bounds.2.1.le] at hlam
        unfold lambdaCountIntegrand
        rw [actual_second_exclusion hN hq hy hc hlam.2, Nat.cast_zero, mul_zero]
      _ = 0 := by simp
  rw [he, mul_zero]

theorem actual_source36_slice {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hc : SecondCase q y) :
    lambdaCountSegment N q y (1 / c1) 0.36 ≤
      profile36 (sourceL N) (Real.log ((q : ℝ) * y)) := by
  have h1 := countSegment_le_cap hN hy (by norm_num : (0 : ℝ) ≤ 0.12)
    (by norm_num : (0.12 : ℝ) ≤ 0.2743) (by norm_num) (C := 2)
    (fun lam hlam => by exact_mod_cast actual_second_count hN hq hy hc hlam.2)
  have h2 := lambdaCountSegment_le_row .r028 hN hq hy (a := 0.2743) (b := 0.28)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h3 := lambdaCountSegment_le_row .r030 hN hq hy (a := 0.28) (b := 0.3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h4 := lambdaCountSegment_le_row .r031 hN hq hy (a := 0.3) (b := 0.31)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h5 := lambdaCountSegment_le_row .r032 hN hq hy (a := 0.31) (b := 0.32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h6 := lambdaCountSegment_le_row .r033 hN hq hy (a := 0.32) (b := 0.33)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h7 := lambdaCountSegment_le_row .r036 hN hq hy (a := 0.33) (b := 0.36)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  norm_num [rowBound, rowMultiplicity, rowSelectedBound] at h2 h3 h4 h5 h6 h7
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 < Real.log ((q : ℝ) * y) := by linarith [original_log_product_ge_ten hN hy]
  rw [countSegment_add hN hy c1_bounds.1.le c1_bounds.2.1.le
      (by norm_num : (0.12 : ℝ) ≤ 0.36) (by norm_num),
    second_lower_segment_zero hN hq hy hc, zero_add]
  have hsplit {a b d : ℝ} := @countSegment_add N q _ hN y a b d hy
  rw [hsplit (by norm_num : (0 : ℝ) ≤ 0.12) (by norm_num : (0.12 : ℝ) ≤ 0.2743)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.2743) (by norm_num : (0.2743 : ℝ) ≤ 0.28)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.28) (by norm_num : (0.28 : ℝ) ≤ 0.3)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.3) (by norm_num : (0.3 : ℝ) ≤ 0.31)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.31) (by norm_num : (0.31 : ℝ) ≤ 0.32)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.32) (by norm_num : (0.32 : ℝ) ≤ 0.33)
      (by norm_num) (by norm_num), profile36_segments hL hs]
  linarith

theorem original_zero_tail_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    lambdaCountSegment N q y 0 0.36 =
      lambdaCountSegment N q y 0 (1 / c1) +
        lambdaCountSegment N q y (1 / c1) 0.36 :=
  countSegment_add hN hy le_rfl c1_bounds.1.le
    (by linarith [c1_bounds.2.1]) (by norm_num)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
