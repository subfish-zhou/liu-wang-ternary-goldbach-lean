import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.TableDomain
import LiuWang.Proof.SourceRoute.ThirdArc.LowWeight

/-! Payment of actual near-one family-count integrals by the admitted table. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

theorem densityBand_zero_eq_count (q : ℕ) [NeZero q] (alpha y : ℝ) :
    densityBand q alpha 0 y 0 = (familyCount q alpha y : ℝ) := by
  simp [densityBand, bandValues, familyCount, count, Nat.cast_sum]

theorem family_beta_integrable (q : ℕ) [NeZero q] (y : ℝ)
    {X a b : ℝ} (hX : 0 < X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun alpha => betaKernel X alpha * familyCount q alpha y)
      volume a b := by
  simpa only [densityBand_zero_eq_count] using
    densityBand_beta_integrable q 0 y 0 hX ha hab

def countIntegral (q : ℕ) [NeZero q] (X y a b : ℝ) : ℝ :=
  ∫ alpha in a..b, betaKernel X alpha * familyCount q alpha y

theorem countIntegral_split (q : ℕ) [NeZero q] (y : ℝ)
    {X a b c : ℝ} (hX : 0 < X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    countIntegral q X y a c = countIntegral q X y a b + countIntegral q X y b c := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (family_beta_integrable q y hX ha hab)
    (family_beta_integrable q y hX (ha.trans hab) hbc)).symm

theorem countIntegral_row (r : DensityRow) {q : ℕ} [NeZero q] {X z y a b : ℝ}
    (hX : 1 ≤ X) (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : rowCutoff r z ≤ a) (hab : a ≤ b) :
    countIntegral q X y a b ≤ (rowBound r : ℝ) * (X ^ (b - 1) - X ^ (a - 1)) := by
  have hx : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hhalf := (rowCutoff_ge_half r hz).trans ha
  calc
    _ ≤ ∫ alpha in a..b, (rowBound r : ℝ) * betaKernel X alpha := by
      apply intervalIntegral.integral_mono_on hab
        (family_beta_integrable q y hx hhalf hab)
        (((betaKernel_continuous hx).intervalIntegrable a b).const_mul _)
      intro alpha halpha
      have hc : (familyCount q alpha y : ℝ) ≤ rowBound r := by
        exact_mod_cast NearOneDensity.Continuation.familyCount_row_tail r hz hqy
          (ha.trans halpha.1)
      have hk : 0 ≤ betaKernel X alpha :=
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg hX)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc hk
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_betaKernel hx]

theorem M3_countIntegral_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y a b : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y)
    (ha : rowCutoff r ((q : ℝ) * y) ≤ a) (hab : a ≤ b) :
    countIntegral q X y a b ≤ (rowBound r : ℝ) * (X ^ (b - 1) - X ^ (a - 1)) :=
  countIntegral_row r hX (M3_table_domain hN hq hy).1 (M3_table_domain hN hq hy).2 ha hab

theorem cutoff_power_exp {X z d : ℝ} (hX : 0 < X) :
    X ^ ((1 - d / Real.log z) - 1) = Real.exp (-d * Real.log X / Real.log z) := by
  rw [Real.rpow_def_of_pos hX]
  congr 1
  ring

theorem M3_near_one_integral_paid (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y d : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y)
    (_hd : 0 ≤ d) (hdr : d ≤ rowLambda r) :
    countIntegral q X y (rowCutoff r ((q : ℝ) * y))
        (1 - d / Real.log ((q : ℝ) * y)) ≤
      (rowBound r : ℝ) *
        (Real.exp (-d * Real.log X / Real.log ((q : ℝ) * y)) -
          Real.exp (-rowLambda r * Real.log X / Real.log ((q : ℝ) * y))) := by
  have hz := (M3_table_domain hN hq hy).1
  have hl : 0 ≤ Real.log ((q : ℝ) * y) := Real.log_nonneg (by linarith)
  have hab : rowCutoff r ((q : ℝ) * y) ≤ 1 - d / Real.log ((q : ℝ) * y) := by
    exact sub_le_sub_left (div_le_div_of_nonneg_right hdr hl) 1
  have h := M3_countIntegral_row r hN hq hX hy le_rfl hab
  simpa only [rowCutoff, cutoff_power_exp (lt_of_lt_of_le zero_lt_one hX)] using h

theorem M3_0478_integral_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y) :
    countIntegral q X y (1 - 0.478 / Real.log ((q : ℝ) * y)) 1 ≤
      14000 * (1 - Real.exp (-0.478 * Real.log X / Real.log ((q : ℝ) * y))) := by
  have h := M3_near_one_integral_paid .r0478 hN hq hX hy (d := 0)
    (by norm_num) (by norm_num [rowLambda])
  norm_num only [rowCutoff, rowLambda, rowBound, rowMultiplicity, rowSelectedBound,
    Nat.cast_mul, Nat.cast_ofNat, neg_zero, zero_mul, zero_div, sub_zero, Real.exp_zero] at h ⊢
  exact h

theorem family_low_integrable (q : ℕ) [NeZero q] (y : ℝ)
    {X a b : ℝ} (hX : 0 < X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun alpha =>
      (betaKernel X alpha * lowCoefficient alpha) * familyCount q alpha y) volume a b := by
  have hc : ContinuousOn lowCoefficient (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact lowCoefficient_continuousOn (by linarith)
  have h := (family_beta_integrable q y hX ha hab).mul_continuousOn hc
  convert h using 1
  ext alpha
  ring

theorem M3_low_integral_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y a b c : ℝ} (hy : lowHeight ≤ y)
    (ha : rowCutoff r ((q : ℝ) * y) ≤ a) (hab : a ≤ b)
    (hc : 0 < c) (hca : c ≤ a) :
    (∫ alpha in a..b,
      (betaKernel N alpha * lowCoefficient alpha) * familyCount q alpha y) ≤
      lowCoefficient c * ((rowBound r : ℝ) *
        ((N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1))) := by
  have hx := natCast_pos_of_exp_le hN
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hh := (rowCutoff_ge_half r (M3_table_domain hN hq hy).1).trans ha
  calc
    _ ≤ ∫ alpha in a..b, lowCoefficient c * (betaKernel N alpha * familyCount q alpha y) := by
      apply intervalIntegral.integral_mono_on hab (family_low_integrable q y hx hh hab)
        ((family_beta_integrable q y hx hh hab).const_mul _)
      intro alpha halpha
      have hk : 0 ≤ betaKernel N alpha * (familyCount q alpha y : ℝ) :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg hX)) (Nat.cast_nonneg _)
      have h := mul_le_mul_of_nonneg_right
        (lowCoefficient_antitone hc (hca.trans halpha.1)) hk
      exact (show (betaKernel N alpha * lowCoefficient alpha) *
        (familyCount q alpha y : ℝ) = lowCoefficient alpha *
          (betaKernel N alpha * familyCount q alpha y) by ring).trans_le h
    _ = lowCoefficient c * countIntegral q N y a b := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (M3_countIntegral_row r hN hq hX hy ha hab)
      (lowCoefficient_nonneg hc)

theorem original_low_0478_subinterval {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    (∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * lowHeight))..
        (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)),
      (betaKernel N alpha * lowCoefficient alpha) * familyCount q alpha lowHeight) ≤
      lowCoefficient (59 / 60) *
        (14000 * ((N : ℝ) ^ (-0.2067 / Real.log ((q : ℝ) * lowHeight)) -
          (N : ℝ) ^ (-0.478 / Real.log ((q : ℝ) * lowHeight)))) := by
  have hz := (low_table_domain hN hq).1
  have hl : 0 ≤ Real.log ((q : ℝ) * lowHeight) := Real.log_nonneg (by linarith)
  have hab : 1 - 0.478 / Real.log ((q : ℝ) * lowHeight) ≤
      1 - 0.2067 / Real.log ((q : ℝ) * lowHeight) :=
    sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hl) 1
  have h := M3_low_integral_row .r0478 hN hq le_rfl le_rfl hab (c := 59 / 60)
    (by norm_num) (M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl)
  norm_num only [rowCutoff, rowLambda, rowBound, rowMultiplicity, rowSelectedBound,
    Nat.cast_mul, Nat.cast_ofNat, sub_sub_cancel_left, neg_div] at h ⊢
  exact h

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
