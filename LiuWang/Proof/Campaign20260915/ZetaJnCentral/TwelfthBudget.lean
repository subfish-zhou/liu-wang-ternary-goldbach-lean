import LiuWang.Proof.Campaign20260915.ZetaJnCentral.TwelfthOuter

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem exp_three_eighths_le : Real.exp (3 / 8) ≤ 3 / 2 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hpow : Real.exp (3 / 8) ^ 8 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  rw [hpow]
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (show Real.exp 1 ≤ 68 / 25 by linarith [Real.exp_one_lt_d9]) 3
  exact h.trans (by norm_num)

theorem twelfth_exp_seed :
    Real.exp (-Real.pi / 3 * (10 / 3 : ℝ) ^ 2) ≤ 1 / 111000 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 314 / 27) 24
  have hlo : (111000 : ℝ) ≤ Real.exp (314 / 27) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith
  have hx : (314 / 27 : ℝ) ≤ Real.pi / 3 * (10 / 3) ^ 2 := by linarith [Real.pi_gt_d2]
  have hh := hlo.trans (Real.exp_le_exp.mpr hx)
  rw [show -Real.pi / 3 * (10 / 3 : ℝ) ^ 2 = -(Real.pi / 3 * (10 / 3) ^ 2) by ring,
    Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hh

theorem twelfth_exp_seed_three :
    Real.exp (-Real.pi * (10 / 3 : ℝ) ^ 2) ≤ 1 / (111000 : ℝ) ^ 3 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le twelfth_exp_seed 3
  have he : Real.exp (-Real.pi / 3 * (10 / 3 : ℝ) ^ 2) ^ 3 =
      Real.exp (-Real.pi * (10 / 3 : ℝ) ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he] at h
  simpa only [div_pow, one_pow] using h

theorem twelfth_denominator {d : ℝ} (hd : 10 / 3 ≤ d) :
    99 / 100 ≤ 1 - Real.exp (-Real.sqrt 2 * Real.pi * d) := by
  have hs : 7 / 5 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hc : 21 / 5 ≤ Real.sqrt 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hx : 14 ≤ Real.sqrt 2 * Real.pi * d := by nlinarith
  have he := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ Real.sqrt 2 * Real.pi * d)
  have hlo : 100 ≤ Real.exp (Real.sqrt 2 * Real.pi * d) := by nlinarith
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hlo
  have heq : Real.exp (-Real.sqrt 2 * Real.pi * d) =
      1 / Real.exp (Real.sqrt 2 * Real.pi * d) := by
    rw [show -Real.sqrt 2 * Real.pi * d = -(Real.sqrt 2 * Real.pi * d) by ring,
      Real.exp_neg, one_div]
  rw [heq]
  linarith

theorem twelfthOuterBudget_source {eta : ℝ} (he : 44 ≤ eta) :
    twelfthOuterBudget eta ≤ (1 / 3) / eta ^ 3 := by
  let d := twelfthCutoff eta
  let K : ℝ := (32 / 27 : ℝ) ^ 3
  have hd : 10 / 3 ≤ d := (twelfthRadius_data he).2.1
  have hd0 : 0 < d := by linarith
  have he0 : 0 < eta := by linarith
  have hden := twelfth_denominator hd
  have hden0 := exterior_denominator_pos hd0
  have hEta : eta = (32 / 27) * d ^ 3 := by
    have h := (twelfthRadius_data he).2.2.2
    change d ^ 3 = 27 / 32 * eta at h
    linarith
  have hp : eta ^ 3 = K * d ^ 9 := by
    rw [hEta, mul_pow]
    dsimp [K]
    ring
  have hmono1 := powerGaussian_antitone 8 (by positivity : 0 < Real.pi / 3)
    (by norm_num : (0 : ℝ) ≤ 10 / 3) (by norm_num; linarith [Real.pi_gt_three])
  have hmono3 := powerGaussian_antitone 8 Real.pi_pos
    (by norm_num : (0 : ℝ) ≤ 10 / 3) (by norm_num; linarith [Real.pi_gt_three])
  have h1 : d ^ 8 * Real.exp (-Real.pi / 3 * d ^ 2) ≤ (10 / 3 : ℝ) ^ 8 / 111000 := by
    have h := hmono1 (by simp) hd hd
    dsimp only at h
    simp only [neg_div] at h ⊢
    apply h.trans
    simpa only [neg_div, mul_one_div] using mul_le_mul_of_nonneg_left twelfth_exp_seed
      (by norm_num : (0 : ℝ) ≤ (10 / 3) ^ 8)
  have h3 : d ^ 8 * Real.exp (-Real.pi * d ^ 2) ≤ (10 / 3 : ℝ) ^ 8 / (111000 : ℝ) ^ 3 := by
    have h := hmono3 (by simp) hd hd
    dsimp only at h
    apply h.trans
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left twelfth_exp_seed_three
      (by norm_num : (0 : ℝ) ≤ (10 / 3) ^ 8)
  have hpi : 1 / Real.pi ≤ 50 / 157 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_d2]
  have hc1 : Real.exp (3 / 8) * 3 / Real.pi * K ≤ (3 / 2) * (150 / 157) * K := by
    have h := mul_le_mul exp_three_eighths_le
      (mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 3))
      (by positivity : (0 : ℝ) ≤ 3 * (1 / Real.pi)) (by norm_num)
    have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ K by dsimp [K]; positivity)
    calc
      _ = (Real.exp (3 / 8) * (3 * (1 / Real.pi))) * K := by ring
      _ ≤ ((3 / 2) * (3 * (50 / 157))) * K := hh
      _ = _ := by ring
  have hc3 : 1200 / Real.pi * K ≤ 1200 * (50 / 157) * K := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 1200)) (by dsimp [K]; positivity)
  have hs := add_le_add
    (mul_le_mul hc1 h1 (by positivity) (by dsimp [K]; positivity))
    (mul_le_mul hc3 h3 (by positivity) (by dsimp [K]; positivity))
  have hsmall :
      (Real.exp (3 / 8) * 3 / Real.pi * K) * (d ^ 8 * Real.exp (-Real.pi / 3 * d ^ 2)) +
        (1200 / Real.pi * K) * (d ^ 8 * Real.exp (-Real.pi * d ^ 2)) ≤ 33 / 100 := by
    apply hs.trans
    norm_num [K]
  rw [le_div_iff₀ (by positivity : 0 < eta ^ 3)]
  have hid : twelfthOuterBudget eta * eta ^ 3 =
      ((Real.exp (3 / 8) * 3 / Real.pi * K) * (d ^ 8 * Real.exp (-Real.pi / 3 * d ^ 2)) +
        (1200 / Real.pi * K) * (d ^ 8 * Real.exp (-Real.pi * d ^ 2))) /
          (1 - Real.exp (-Real.sqrt 2 * Real.pi * d)) := by
    change ((Real.exp (3 / 8) * (3 / (Real.pi * d)) * Real.exp (-Real.pi / 3 * d ^ 2) +
      1200 / (Real.pi * d) * Real.exp (-Real.pi * d ^ 2)) /
      (1 - Real.exp (-Real.sqrt 2 * Real.pi * d))) * eta ^ 3 = _
    rw [hp]
    have hdne := hd0.ne'
    field_simp
  rw [hid, div_le_iff₀ hden0]
  linarith

theorem jn_twelfth_source_budget {eta : ℝ} {m : ℕ} (he : 44 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 12 y‖ ≤
      (51 / 100) / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have hd : 0 < twelfthCutoff eta := by linarith [(twelfthRadius_data he).2.1]
  have hs := jn_local_split (1 / 2) he0 hd.le (twelfthRadius_data he).2.2.1 hm0 hm1 11
  have hc := jn_twelfth_central he hm0 hm1
  have ho := (jn_twelfth_outer he hm0 hm1).trans (twelfthOuterBudget_source he)
  simp only [Nat.reduceAdd, neg_div] at hs hc ho ⊢
  rw [hs, norm_neg]
  apply norm_add₃_le.trans
  have ha : (15 / 2) / eta ^ 4 + (1 / 3) / eta ^ 3 ≤ (51 / 100) / eta ^ 3 := by
    have hn : eta ^ 4 = eta * eta ^ 3 := by ring
    rw [hn]
    field_simp
    nlinarith
  exact (show _ ≤ (15 / 2) / eta ^ 4 + (1 / 3) / eta ^ 3 by linarith).trans ha

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
