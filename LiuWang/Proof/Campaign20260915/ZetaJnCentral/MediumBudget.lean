import LiuWang.Proof.Campaign20260915.ZetaJnCentral.MediumOuter
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.TwelfthBudget

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem medium_exp_seed :
    Real.exp (-Real.pi / 3 * (21 / 10 : ℝ) ^ 2) ≤ 1 / 100 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 23079 / 5000) 17
  have hlo : (100 : ℝ) ≤ Real.exp (23079 / 5000) := by
    norm_num [Finset.sum_range_succ] at hs
    linarith
  have hx : (23079 / 5000 : ℝ) ≤ Real.pi / 3 * (21 / 10) ^ 2 := by linarith [Real.pi_gt_d2]
  have hh := hlo.trans (Real.exp_le_exp.mpr hx)
  rw [show -Real.pi / 3 * (21 / 10 : ℝ) ^ 2 = -(Real.pi / 3 * (21 / 10) ^ 2) by ring,
    Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hh

theorem medium_exp_seed_three :
    Real.exp (-Real.pi * (21 / 10 : ℝ) ^ 2) ≤ 1 / (100 : ℝ) ^ 3 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le medium_exp_seed 3
  have he : Real.exp (-Real.pi / 3 * (21 / 10 : ℝ) ^ 2) ^ 3 =
      Real.exp (-Real.pi * (21 / 10 : ℝ) ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he] at h
  simpa only [div_pow, one_pow] using h

theorem outer_denominator_99 {d : ℝ} (hd : 2 ≤ d) :
    99 / 100 ≤ 1 - Real.exp (-Real.sqrt 2 * Real.pi * d) := by
  have hs : 7 / 5 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hc : 21 / 5 ≤ Real.sqrt 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hx : 8 ≤ Real.sqrt 2 * Real.pi * d := by nlinarith
  have he8 : (256 : ℝ) ≤ Real.exp 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le 8
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have hlo : 100 ≤ Real.exp (Real.sqrt 2 * Real.pi * d) :=
    (by norm_num : (100 : ℝ) ≤ 256).trans (he8.trans (Real.exp_le_exp.mpr hx))
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hlo
  have heq : Real.exp (-Real.sqrt 2 * Real.pi * d) =
      1 / Real.exp (Real.sqrt 2 * Real.pi * d) := by
    rw [show -Real.sqrt 2 * Real.pi * d = -(Real.sqrt 2 * Real.pi * d) by ring,
      Real.exp_neg, one_div]
  rw [heq]
  linarith

theorem mediumOuterBudget_source {eta : ℝ} (he : 11 ≤ eta) :
    mediumOuterBudget eta ≤ (43 / 500) / eta := by
  let d := twelfthCutoff eta
  have hd : 21 / 10 ≤ d := (mediumRadius_data he).2.1
  have hd0 : 0 < d := by linarith
  have he0 : 0 < eta := by linarith
  have hden := outer_denominator_99 (by linarith : 2 ≤ d)
  have hden0 := exterior_denominator_pos hd0
  have hEta : eta = (32 / 27) * d ^ 3 := by
    have h := (mediumRadius_data he).2.2.2
    change d ^ 3 = 27 / 32 * eta at h
    linarith
  have hmono1 := powerGaussian_antitone 2 (by positivity : 0 < Real.pi / 3)
    (by norm_num : (0 : ℝ) ≤ 21 / 10) (by norm_num; linarith [Real.pi_gt_three])
  have hmono3 := powerGaussian_antitone 2 Real.pi_pos
    (by norm_num : (0 : ℝ) ≤ 21 / 10) (by norm_num; linarith [Real.pi_gt_three])
  have h1 : d ^ 2 * Real.exp (-Real.pi / 3 * d ^ 2) ≤ (21 / 10 : ℝ) ^ 2 / 100 := by
    have h := hmono1 (by simp) hd hd
    dsimp only at h
    simp only [neg_div] at h ⊢
    apply h.trans
    simpa only [neg_div, mul_one_div] using mul_le_mul_of_nonneg_left medium_exp_seed
      (by norm_num : (0 : ℝ) ≤ (21 / 10) ^ 2)
  have h3 : d ^ 2 * Real.exp (-Real.pi * d ^ 2) ≤ (21 / 10 : ℝ) ^ 2 / (100 : ℝ) ^ 3 := by
    have h := hmono3 (by simp) hd hd
    dsimp only at h
    apply h.trans
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left medium_exp_seed_three
      (by norm_num : (0 : ℝ) ≤ (21 / 10) ^ 2)
  have hpi : 1 / Real.pi ≤ 50 / 157 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_d2]
  have hc1 : Real.exp (3 / 8) * 3 / Real.pi * (32 / 27) ≤ (3 / 2) * (150 / 157) * (32 / 27) := by
    have h := mul_le_mul exp_three_eighths_le
      (mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 3))
      (by positivity : (0 : ℝ) ≤ 3 * (1 / Real.pi)) (by norm_num)
    have hh := mul_le_mul_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 32 / 27)
    calc
      _ = (Real.exp (3 / 8) * (3 * (1 / Real.pi))) * (32 / 27) := by ring
      _ ≤ ((3 / 2) * (3 * (50 / 157))) * (32 / 27) := hh
      _ = _ := by ring
  have hc3 : 6000 / Real.pi * (32 / 27) ≤ 6000 * (50 / 157) * (32 / 27) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 6000)) (by norm_num : (0 : ℝ) ≤ 32 / 27)
  have hs := add_le_add (mul_le_mul hc1 h1 (by positivity) (by norm_num))
    (mul_le_mul hc3 h3 (by positivity) (by norm_num))
  have hsmall :
      (Real.exp (3 / 8) * 3 / Real.pi * (32 / 27)) * (d ^ 2 * Real.exp (-Real.pi / 3 * d ^ 2)) +
        (6000 / Real.pi * (32 / 27)) * (d ^ 2 * Real.exp (-Real.pi * d ^ 2)) ≤ 4257 / 50000 := by
    exact hs.trans (by norm_num)
  rw [le_div_iff₀ he0]
  have hid : mediumOuterBudget eta * eta =
      ((Real.exp (3 / 8) * 3 / Real.pi * (32 / 27)) * (d ^ 2 * Real.exp (-Real.pi / 3 * d ^ 2)) +
        (6000 / Real.pi * (32 / 27)) * (d ^ 2 * Real.exp (-Real.pi * d ^ 2))) /
          (1 - Real.exp (-Real.sqrt 2 * Real.pi * d)) := by
    change ((Real.exp (3 / 8) * (3 / (Real.pi * d)) * Real.exp (-Real.pi / 3 * d ^ 2) +
      6000 / (Real.pi * d) * Real.exp (-Real.pi * d ^ 2)) /
      (1 - Real.exp (-Real.sqrt 2 * Real.pi * d))) * eta = _
    rw [hEta]
    have hdne := hd0.ne'
    field_simp
  rw [hid, div_le_iff₀ hden0]
  linarith

theorem jn_medium_source_budget {eta : ℝ} {m : ℕ} (he : 11 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 12 y‖ ≤
      (23 / 200) / eta := by
  have he0 : 0 < eta := by linarith
  have hd : 0 < twelfthCutoff eta := by linarith [(mediumRadius_data he).2.1]
  have hs := jn_local_split (1 / 2) he0 hd.le (mediumRadius_data he).2.2.1 hm0 hm1 11
  have hc := jn_medium_central he hm0 hm1
  have ho := (jn_medium_outer he hm0 hm1).trans (mediumOuterBudget_source he)
  simp only [Nat.reduceAdd, neg_div] at hs hc ho ⊢
  rw [hs, norm_neg]
  apply norm_add₃_le.trans
  have ha : (75 / 2) / eta ^ 4 + (43 / 500) / eta ≤ (23 / 200) / eta := by
    have hn : eta ^ 4 = eta * eta ^ 3 := by ring
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) he 3
    norm_num at hp
    rw [hn]
    field_simp
    nlinarith
  exact (show _ ≤ (75 / 2) / eta ^ 4 + (43 / 500) / eta by linarith).trans ha

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
