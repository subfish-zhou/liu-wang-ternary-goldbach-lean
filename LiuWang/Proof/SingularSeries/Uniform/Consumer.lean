import LiuWang.Proof.SingularSeries.Uniform.Tail

/-!
# Paid arithmetic errors in the original pure main term

The unconditional lower bound contains neither the coefficient tail nor
the weighted totient sum. Its only unevaluated constant is the proved
positive universal odd-prime product. The decimal endpoint is proved
conditional only on the explicitly unproved finite-certificate gate.
-/

set_option autoImplicit false
noncomputable section
open Finset
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SingularSeries.Uniform

theorem sourceP_lower {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (3100 : ℝ) ^ 3 ≤ sourceP N :=
  pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 3

theorem sourceP_ge_one {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 ≤ sourceP N := (by norm_num : (1 : ℝ) ≤ 3100 ^ 3).trans (sourceP_lower hN)

theorem source_weightedTotientSum_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedTotientSum (sourceP N) ≤ 22 * sourceP N :=
  weightedTotientSum_le (le_trans (by norm_num) (sourceP_ge_one hN))

theorem source_absoluteTail_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    absoluteTail N (sourceP N) ≤ (1.5 : ℝ) * 10 ^ (-9 : ℤ) := by
  calc
    _ ≤ 44 / sourceP N := absoluteTail_le N (sourceP_ge_one hN)
    _ ≤ 44 / (3100 : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sourceP_lower hN)
    _ ≤ _ := by norm_num

theorem source_coefficientTail_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖coefficientTail N (sourceP N)‖ ≤ (1.5 : ℝ) * 10 ^ (-9 : ℤ) :=
  (coefficientTail_norm_le (nat_pos_of_exp_le hN) _).trans (source_absoluteTail_le hN)

theorem source_partialSeries_error_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    |series N - partialSeries N (sourceP N)| ≤ (1.5 : ℝ) * 10 ^ (-9 : ℤ) :=
  (partialSeries_error_le (nat_pos_of_exp_le hN)
    (le_trans (by norm_num) (sourceP_ge_one hN))).trans (source_absoluteTail_le hN)

theorem source_weighted_arc_expression_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    2.82 * (N : ℝ) ^ 2 / sourceP N ^ 2 * weightedTotientSum (sourceP N) ≤
      62.04 * (N : ℝ) ^ 2 / sourceP N := by
  have hP : 0 < sourceP N := lt_of_lt_of_le (by norm_num) (sourceP_ge_one hN)
  calc
    _ ≤ 2.82 * (N : ℝ) ^ 2 / sourceP N ^ 2 * (22 * sourceP N) :=
      mul_le_mul_of_nonneg_left (source_weightedTotientSum_le hN) (by positivity)
    _ = _ := by field_simp; ring

theorem source_arcError_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖arcError N‖ ≤ 62.04 * (N : ℝ) ^ 2 / sourceP N :=
  (arcError_bound hN).trans (source_weighted_arc_expression_le hN)

theorem re_I11_arithmetic_errors_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    ((0.997 : ℝ) ^ 2 * universalProduct -
      (0.997 : ℝ) ^ 2 / 2 * (44 / sourceP N) -
      62.04 / sourceP N) * (N : ℝ) ^ 2 ≤ (I11 N).re := by
  have h := re_I11_uniform_lower_bound hN hodd
  have ht := mul_le_mul_of_nonneg_left
    (absoluteTail_le N (sourceP_ge_one hN)) (fullMass_nonneg N)
  have hw := source_weighted_arc_expression_le hN
  have hpaid :
      fullMass N * (2 * universalProduct) -
        fullMass N * (44 / sourceP N) -
        62.04 * (N : ℝ) ^ 2 / sourceP N ≤ (I11 N).re := by linarith
  convert hpaid using 1
  unfold fullMass
  ring

theorem re_I11_only_universal_product {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    ((0.997 : ℝ) ^ 2 * universalProduct -
      (0.997 : ℝ) ^ 2 / 2 * ((1.5 : ℝ) * 10 ^ (-9 : ℤ)) -
      62.04 / (3100 : ℝ) ^ 3) * (N : ℝ) ^ 2 ≤ (I11 N).re := by
  have h := re_I11_uniform_lower_bound hN hodd
  have ht := mul_le_mul_of_nonneg_left (source_absoluteTail_le hN) (fullMass_nonneg N)
  have hw := (source_weighted_arc_expression_le hN).trans
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) (sourceP_lower hN))
  have hpaid :
      fullMass N * (2 * universalProduct) -
        fullMass N * ((1.5 : ℝ) * 10 ^ (-9 : ℤ)) -
        62.04 * (N : ℝ) ^ 2 / (3100 : ℝ) ^ 3 ≤ (I11 N).re := by linarith
  convert hpaid using 1
  unfold fullMass
  ring

theorem decimal_margin :
    (0.656145 : ℝ) ≤
      (0.997 : ℝ) ^ 2 * 0.6601 -
      (0.997 : ℝ) ^ 2 / 2 * ((1.5 : ℝ) * 10 ^ (-9 : ℤ)) -
      62.04 / (3100 : ℝ) ^ 3 := by norm_num

theorem re_I11_of_universal_decimal
    (hU : (0.6601 : ℝ) ≤ universalProduct) {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.656145 * (N : ℝ) ^ 2 ≤ (I11 N).re := by
  apply le_trans _ (re_I11_only_universal_product hN hodd)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hU (sq_nonneg (0.997 : ℝ))
  linarith [decimal_margin]

theorem re_I11_of_finite_certificate
    (hfinite : (6601 : ℝ) / 10000 * (20000 / 19999 : ℝ) ≤ universalTruncated 20000)
    {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.656145 * (N : ℝ) ^ 2 ≤ (I11 N).re :=
  re_I11_of_universal_decimal (universal_decimal_of_finite_certificate hfinite) hN hodd

example (X : ℕ) :
    (∑ q ∈ Icc 1 X, ((q : ℝ) / (q.totient : ℝ)) ^ 2) ≤ 22 * (X : ℝ) :=
  ratioSquare_sum_le X

example (N : ℕ) {P : ℝ} (hP : 1 ≤ P) : absoluteTail N P ≤ 44 / P :=
  absoluteTail_le N hP

end LiuWang.Proof.SingularSeries.Uniform
