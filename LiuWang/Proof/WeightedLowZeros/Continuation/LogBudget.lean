import LiuWang.Proof.WeightedLowZeros.SourceBulk

/-! # Uniform elementary exponential payments at the original threshold -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.WeightedLowZeros.Continuation

theorem log_seed_upper : Real.log (3.36 * (3100 : ℝ)^3) ≤ 25.33 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.33) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hs' : (1.3909 : ℝ) ≤ Real.exp 0.33 := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 25
  calc
    _ ≤ (2.7182818283 : ℝ)^25 * 1.3909 := by norm_num
    _ ≤ Real.exp 1 ^25 * Real.exp 0.33 :=
      mul_le_mul hp hs' (by norm_num) (by positivity)
    _ = Real.exp 25.33 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num

theorem exp_neg_seed_upper : Real.exp (-58.49 : ℝ) ≤ 4e-26 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.49) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hs' : (1.63 : ℝ) ≤ Real.exp 0.49 := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 58
  have he : (25000000000000000000000000 : ℝ) ≤ Real.exp 58.49 := by
    calc
      _ ≤ (2.7182818283 : ℝ)^58 * 1.63 := by norm_num
      _ ≤ Real.exp 1 ^58 * Real.exp 0.49 :=
        mul_le_mul hp hs' (by norm_num) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [Real.exp_neg]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 25000000000000000000000000) he
  norm_num at h ⊢
  exact h

theorem log_3100_bounds : 8 ≤ Real.log (3100 : ℝ) ∧ Real.log (3100 : ℝ) ≤ 8.04 := by
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 8
    calc
      Real.exp 8 = Real.exp 1 ^8 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.7182818286 : ℝ)^8 := h
      _ ≤ _ := by norm_num
  · apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      Real.exp_one_gt_d9.le 8
    have hs := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.04)
    calc
      (3100 : ℝ) ≤ (2.7182818283 : ℝ)^8 * (1 + 0.04 + 0.04^2 / 2) := by norm_num
      _ ≤ Real.exp 1 ^8 * Real.exp 0.04 := mul_le_mul hp hs (by norm_num) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem log_scale_bounds {L : ℝ} (hL : 3100 ≤ L) :
    25 ≤ Real.log (3.36 * L^3) ∧
      Real.log (3.36 * L^3) ≤ 25.33 + 3 * Real.log (L / 3100) := by
  have hp : 0 < L := by linarith
  have hlog : 8 ≤ Real.log L := log_3100_bounds.1.trans
    (Real.log_le_log (by norm_num) hL)
  have h336 : 1 ≤ Real.log (3.36 : ℝ) := by
    apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    linarith [Real.exp_one_lt_d9]
  have hid : Real.log (3.36 * L^3) =
      Real.log (3.36 * (3100 : ℝ)^3) + 3 * Real.log (L / 3100) := by
    rw [Real.log_mul (by norm_num) (pow_pos hp 3).ne',
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
      Real.log_div hp.ne' (by norm_num)]
    ring
  constructor
  · rw [Real.log_mul (by norm_num) (pow_pos hp 3).ne', Real.log_pow]
    norm_num
    linarith
  · rw [hid]
    linarith [log_seed_upper]

theorem source_decay_power {L : ℝ} (hL : 3100 ≤ L) :
    Real.exp (-0.478 * L / Real.log (3.36 * L^3)) ≤
      4e-26 * (3100 / L)^5 := by
  let z := Real.log (L / 3100)
  have hp : 0 < L := by linarith
  have hz : 0 ≤ z := Real.log_nonneg (by linarith)
  have he : Real.exp z = L / 3100 := Real.exp_log (by positivity)
  have hquad := Real.quadratic_le_exp_of_nonneg hz
  rw [he] at hquad
  obtain ⟨hlo, hhi⟩ := log_scale_bounds hL
  change Real.log (3.36 * L^3) ≤ 25.33 + 3 * z at hhi
  have hprod := mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 58.49 + 5*z)
  have hgap : (58.49 + 5*z) * Real.log (3.36 * L^3) ≤ 0.478 * L := by
    nlinarith [sq_nonneg z]
  have hquot : 58.49 + 5*z ≤ 0.478 * L / Real.log (3.36 * L^3) :=
    (le_div_iff₀ (by linarith)).mpr hgap
  calc
    _ ≤ Real.exp (-58.49 - 5*z) := Real.exp_le_exp.mpr (by
      rw [neg_mul, neg_div]
      linarith)
    _ = Real.exp (-58.49) * (3100 / L)^5 := by
      have he5 : Real.exp (5*z) = Real.exp z ^5 := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul z 5
      rw [Real.exp_sub, he5, he]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right exp_neg_seed_upper (by positivity)

theorem log_over_self_bound {L : ℝ} (hL : 3100 ≤ L) :
    Real.log L / L ≤ 8.04 / 3100 := by
  have hp : 0 < L := by linarith
  have ht := Real.log_le_sub_one_of_pos (show 0 < L / 3100 by positivity)
  rw [Real.log_div hp.ne' (by norm_num)] at ht
  have hlog : Real.log L ≤ 8.04 * L / 3100 := by
    nlinarith [log_3100_bounds.2]
  exact (div_le_iff₀ hp).mpr (by linarith)

end LiuWang.Proof.WeightedLowZeros.Continuation
