import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.HigherConsumers
import LiuWang.Proof.SourceRoute.MajorOrdinary.Assembly

set_option autoImplicit false
noncomputable section
open Finset
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularSeries.Uniform
open LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

theorem third_power_tail_endpoint : (100000 : ℝ) ^ (-2 / 3 : ℝ) ≤ 0.000465 := by
  have he : ((100000 : ℝ) ^ (-2 / 3 : ℝ)) ^ 3 = 1 / (100000 : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num only
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    (by decide : 3 ≠ 0)).mp
  rw [he]
  norm_num

theorem quadratic_low_moment_tail {P : ℝ} (hP : 100000 ≤ P) :
    totientMoment P (1 / 3) ≤ totientMoment 100000 (1 / 3) + 0.012 := by
  have ht := unweighted_tail_le (by norm_num : (1 / 3 : ℝ) < 1)
    (m := 100001) (B := ⌊P⌋₊) (by norm_num)
  have he : (100001 : ℝ) ^ (-2 / 3 : ℝ) ≤ (100000 : ℝ) ^ (-2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
  have hn := third_power_tail_endpoint
  norm_num only at ht he hn
  linarith only [totientMoment_split_le hP (1 / 3), ht, he, hn]

theorem source_inverse_two_thirds {P : ℝ} (hP : 10000000000 ≤ P) :
    P ^ (-2 / 3 : ℝ) ≤ 0.000001 := by
  calc
    _ ≤ P ^ (-3 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ (10000000000 : ℝ) ^ (-3 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hP (by norm_num)
    _ = _ := by
      rw [show (10000000000 : ℝ) = (10 : ℝ) ^ (10 : ℕ) by norm_num,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num

theorem quadratic_high_moment_normalized {P : ℝ} (hP : 10000000000 ≤ P) :
    totientMoment P (4 / 3) / P ≤ 0.000031 := by
  have hp : 0 < P := by linarith
  have h := unweighted_high_prefix_real (by norm_num : (1 : ℝ) < 4 / 3)
    (by norm_num) (show 1 ≤ P by linarith)
  have hm : totientMoment P (4 / 3) ≤ 10.3 * (1 + P ^ (1 / 3 : ℝ) / (1 / 3)) := by
    exact (sum_le_sum (fun q _ => totient_weight_le_unweighted q (4 / 3))).trans
      (by convert! h using 1; norm_num)
  have he : P ^ (1 / 3 : ℝ) / P = P ^ (-2 / 3 : ℝ) := by
    rw [show (-2 / 3 : ℝ) = 1 / 3 - 1 by norm_num, Real.rpow_sub hp, Real.rpow_one]
  have hd := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10000000000) hP
  calc
    _ ≤ (10.3 * (1 + P ^ (1 / 3 : ℝ) / (1 / 3))) / P :=
      div_le_div_of_nonneg_right hm hp.le
    _ = 10.3 * (1 / P) + 30.9 * P ^ (-2 / 3 : ℝ) := by rw [← he]; ring
    _ ≤ 10.3 * (1 / 10000000000) + 30.9 * 0.000001 :=
      add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num))
        (mul_le_mul_of_nonneg_left (source_inverse_two_thirds hP) (by norm_num))
    _ ≤ _ := by norm_num

theorem weighted_linear_sum (P s a b : ℝ) :
    (∑ q ∈ denominators P, totientWeight q s * (a + b * (q : ℝ))) =
      a * totientMoment P s + b * totientMoment P (s + 1) := by
  simp only [totientMoment, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  rw [show s + 1 = s + (1 : ℕ) by simp, totientWeight_shift (mem_Icc.mp hq).1 s 1]
  ring

theorem quadratic_mother_reduction {P : ℝ} (hP : 10000000000 ≤ P) :
    (∑ q ∈ denominators P, totientWeight q (1 / 3) *
      (0.0194 + (0.063 / P) * (q : ℝ)) ^ 2) ≤
      0.0194 ^ 2 * (totientMoment 100000 (1 / 3) + 0.012) +
        ((0.0194 + 0.063) ^ 2 - 0.0194 ^ 2) * 0.000031 := by
  have hp : 0 < P := by linarith
  calc
    _ ≤ ∑ q ∈ denominators P, totientWeight q (1 / 3) *
        (0.0194 ^ 2 + (((0.0194 + 0.063) ^ 2 - 0.0194 ^ 2) / P) * (q : ℝ)) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (totientWeight_nonneg _ _)
      have hqP : (q : ℝ) / P ≤ 1 :=
        (div_le_one hp).mpr ((Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le hp.le))
      have h := quadratic_secant (a := 0.0194) (b := 0.063)
        (div_nonneg (Nat.cast_nonneg q) hp.le) hqP
      convert! h using 1 <;> ring
    _ = 0.0194 ^ 2 * totientMoment P (1 / 3) +
        ((0.0194 + 0.063) ^ 2 - 0.0194 ^ 2) * (totientMoment P (4 / 3) / P) := by
      rw [weighted_linear_sum]
      norm_num only
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (quadratic_low_moment_tail (by linarith)) (by norm_num))
      (mul_le_mul_of_nonneg_left (quadratic_high_moment_normalized hP) (by norm_num))

theorem quadratic_expanded_mothers_reduced {P : ℝ} (hP : 10000000000 ≤ P) :
    0.0194 ^ 2 * totientMoment P (1 / 3) +
      2 * 0.0194 * (0.063 / P) * totientMoment P (4 / 3) +
      (0.063 / P) ^ 2 * totientMoment P (7 / 3) ≤
        0.0194 ^ 2 * (totientMoment 100000 (1 / 3) + 0.012) +
          ((0.0194 + 0.063) ^ 2 - 0.0194 ^ 2) * 0.000031 := by
  have he := quadratic_moment_expansion P (1 / 3) 0.0194 (0.063 / P)
  norm_num only at he ⊢
  rw [← he]
  convert! quadratic_mother_reduction hP using 1 <;> norm_num

theorem quadraticPrefactor_le : quadraticPrefactor ≤ 1.056 := by
  have hroot (x : ℝ) (hx : 0 ≤ x) (s : ℝ) :
      (x ^ s) ^ 3 = x ^ (s * 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hc : quadraticPrefactor ^ 3 =
      27 * (3.36 / (5 * Real.pi)) ^ 2 * (2.994006 / Real.pi) := by
    unfold quadraticPrefactor
    rw [mul_pow, mul_pow, hroot _ (by positivity), hroot _ (by positivity)]
    norm_num
  have hp : (3.141592 : ℝ) ≤ Real.pi := Real.pi_gt_d6.le
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3.36)
    (by norm_num : (0 : ℝ) < 5 * 3.141592) (mul_le_mul_of_nonneg_left hp (by norm_num))
  have ha := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2.994006)
    (by norm_num : (0 : ℝ) < 3.141592) hp
  apply (pow_le_pow_iff_left₀ (by unfold quadraticPrefactor; positivity)
    (by norm_num) (by decide : 3 ≠ 0)).mp
  rw [hc]
  calc
    _ ≤ 27 * (3.36 / (5 * 3.141592)) ^ 2 * (2.994006 / 3.141592) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hd 2) (by norm_num))
        ha (by positivity) (by norm_num)
    _ ≤ _ := by norm_num

theorem I13_literal_head_no_RS {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    ‖I13 N‖ ≤ 1.056 *
      (0.0194 ^ 2 * (totientMoment 100000 (1 / 3) + 0.012) +
        ((0.0194 + 0.063) ^ 2 - 0.0194 ^ 2) * 0.000031) * (N : ℝ) ^ 2 := by
  have hm := quadratic_expanded_mothers_reduced (sourceP_ge_ten_billion hN)
  unfold sourceP at hm
  have hnon : 0 ≤ totientMoment 100000 (1 / 3) :=
    sum_nonneg fun q _ => totientWeight_nonneg q _
  apply (I13_expanded_moments hN hlow hhigh).trans
  apply (mul_le_mul_of_nonneg_left hm
    (by unfold quadraticPrefactor; positivity : 0 ≤ quadraticPrefactor * (N : ℝ) ^ 2)).trans
  have hc := mul_le_mul_of_nonneg_right quadraticPrefactor_le
    (show 0 ≤ 0.0194 ^ 2 * (totientMoment 100000 (1 / 3) + 0.012) +
        ((0.0194 + 0.063) ^ 2 - 0.0194 ^ 2) * 0.000031 by positivity)
  convert! mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ)) using 1
  ring

theorem I13_of_finite_head {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4)
    (hhead : totientMoment 100000 (1 / 3) ≤ 4.01) :
    ‖I13 N‖ ≤ 0.0016 * (N : ℝ) ^ 2 := by
  apply (I13_literal_head_no_RS hN hlow hhigh).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  linarith only [hhead]

theorem ordinary_major_lower_literal_head {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    (0.545324999 - 1.056 *
      (0.0194 ^ 2 * (totientMoment 100000 (1 / 3) + 0.012) +
        ((0.0194 + 0.063) ^ 2 - 0.0194 ^ 2) * 0.000031)) * (N : ℝ) ^ 2 ≤
      (majorIntegral N).re := by
  have h12 := I12_no_RS hN hlow hhigh
  have h13 := I13_literal_head_no_RS hN hlow hhigh
  have h14 := I14_no_RS hN hlow hhigh
  have hr12 := Complex.re_le_norm (-I12 N)
  have hr13 := Complex.re_le_norm (-I13 N)
  have hr14 := Complex.re_le_norm (-I14 N)
  simp only [Complex.neg_re, norm_neg] at hr12 hr13 hr14
  have he := interactionIntegral_split (nat_pos_of_exp_le (exp_2000_le_of_exp_3100_le hN))
  have hmajor := re_major_lower_log_power (exp_2000_le_of_exp_3100_le hN)
  rw [he, Complex.add_re, Complex.add_re] at hmajor
  nlinarith only [h12, h13, h14, hr12, hr13, hr14, hmajor,
    Decimal.re_I11_decimal_lower_bound hN hodd,
    log_power_le_decimal (exp_2000_le_of_exp_3100_le hN), sq_nonneg (N : ℝ)]

theorem ordinary_major_lower_of_finite_head {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4)
    (hhead : totientMoment 100000 (1 / 3) ≤ 4.01) :
    0.5437 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re := by
  have h12 := I12_no_RS hN hlow hhigh
  have h13 := I13_of_finite_head hN hlow hhigh hhead
  have h14 := I14_no_RS hN hlow hhigh
  have hr12 := Complex.re_le_norm (-I12 N)
  have hr13 := Complex.re_le_norm (-I13 N)
  have hr14 := Complex.re_le_norm (-I14 N)
  simp only [Complex.neg_re, norm_neg] at hr12 hr13 hr14
  have he := interactionIntegral_split (nat_pos_of_exp_le (exp_2000_le_of_exp_3100_le hN))
  have hmajor := re_major_lower_log_power (exp_2000_le_of_exp_3100_le hN)
  rw [he, Complex.add_re, Complex.add_re] at hmajor
  nlinarith only [h12, h13, h14, hr12, hr13, hr14, hmajor,
    Decimal.re_I11_decimal_lower_bound hN hodd,
    log_power_le_decimal (exp_2000_le_of_exp_3100_le hN), sq_nonneg (N : ℝ)]

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart
