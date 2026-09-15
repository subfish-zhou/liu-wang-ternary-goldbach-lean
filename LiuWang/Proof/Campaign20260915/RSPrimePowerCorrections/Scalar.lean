import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.Raw
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

noncomputable section

open Finset

namespace LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

theorem root_ratio_bound {x B c : ℝ} {k : ℕ}
    (hB : 0 ≤ B) (hx : B ≤ x) (hc : 0 ≤ c) (hk : 3 ≤ k)
    (hcert : 1 ≤ c ^ (3 * k) * B ^ (k - 3)) :
    x ^ (1 / (k : ℝ)) ≤ c * x ^ (1 / (3 : ℝ)) := by
  have hx0 := hB.trans hx
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (x ^ (1 / (k : ℝ))) ^ (3 * k) = x ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast hx0]
    have he : (1 / (k : ℝ)) * (3 * k : ℕ) = 3 := by
      push_cast
      field_simp
    rw [he]
    norm_num
  have h2 : (x ^ (1 / (3 : ℝ))) ^ (3 * k) = x ^ k := by
    rw [← Real.rpow_mul_natCast hx0]
    have he : (1 / (3 : ℝ)) * (3 * k : ℕ) = k := by push_cast; ring
    rw [he, Real.rpow_natCast]
  apply le_of_pow_le_pow_left₀ (by omega : 3 * k ≠ 0) (by positivity)
  rw [h1, mul_pow, h2]
  have hpow := pow_le_pow_left₀ hB hx (k - 3)
  have hscale : 1 ≤ c ^ (3 * k) * x ^ (k - 3) :=
    hcert.trans (mul_le_mul_of_nonneg_left hpow (pow_nonneg hc _))
  have h := mul_le_mul_of_nonneg_left hscale (pow_nonneg hx0 3)
  have he : 3 + (k - 3) = k := by omega
  calc
    x ^ (3 : ℕ) ≤ x ^ (3 : ℕ) * (c ^ (3 * k) * x ^ (k - 3)) := by
      simpa only [mul_one] using h
    _ = c ^ (3 * k) * x ^ k := by
      rw [show x ^ k = x ^ (3 : ℕ) * x ^ (k - 3) by rw [← pow_add, he]]
      ring

def middleCoefficient : ℕ → ℚ
  | 3 => 1
  | 4 => 407 / 1024
  | 5 => 117 / 512
  | 6 => 81 / 512
  | 7 => 31 / 256
  | 8 => 51 / 512
  | 9 => 11 / 128
  | 10 => 77 / 1024
  | 11 => 35 / 512
  | 12 => 1 / 16
  | 13 => 15 / 256
  | 14 => 57 / 1024
  | 15 => 27 / 512
  | 16 => 51 / 1024
  | 17 => 49 / 1024
  | 18 => 3 / 64
  | 19 => 23 / 512
  | 20 => 45 / 1024
  | 21 => 11 / 256
  | 22 => 43 / 1024
  | 23 => 21 / 512
  | 24 => 41 / 1024
  | _ => 0

theorem middleCoefficient_certificate :
    ∀ k ∈ Icc 3 24, 0 ≤ middleCoefficient k ∧
      1 ≤ middleCoefficient k ^ (3 * k) * (65536 : ℚ) ^ (k - 3) := by
  decide +kernel

theorem middleCoefficient_sum :
    (∑ k ∈ Icc 3 24, middleCoefficient k) = 733 / 256 := by
  decide +kernel

theorem middle_sum_lt_three {x : ℝ} (hx : 65536 ≤ x) :
    (∑ k ∈ Icc (3 : ℕ) 24, x ^ (1 / (k : ℝ))) < 3 * x ^ (1 / (3 : ℝ)) := by
  have hc : (∑ k ∈ Icc (3 : ℕ) 24, x ^ (1 / (k : ℝ))) ≤
      (733 / 256 : ℝ) * x ^ (1 / (3 : ℝ)) := by
    have he : (∑ k ∈ Icc 3 24, (middleCoefficient k : ℝ)) = 733 / 256 := by
      have h := congrArg (fun q : ℚ => (q : ℝ)) middleCoefficient_sum
      push_cast at h
      exact h
    rw [← he, sum_mul]
    apply sum_le_sum
    intro k hk
    have hcert := middleCoefficient_certificate k hk
    apply root_ratio_bound (by norm_num : (0 : ℝ) ≤ 65536) hx
      (Rat.cast_nonneg.mpr hcert.1) (mem_Icc.mp hk).1
    exact_mod_cast hcert.2
  apply hc.trans_lt
  exact mul_lt_mul_of_pos_right (by norm_num)
    (Real.rpow_pos_of_pos (by linarith) _)

private def largeCoefficient : ℕ → ℚ
  | 3 => 1
  | 4 => 1 / 4
  | 5 => 1 / 8
  | 6 => 1 / 16
  | 7 => 1 / 16
  | 8 => 1 / 32
  | _ => 0

private theorem largeCoefficient_certificate :
    ∀ k ∈ Icc 3 8, 0 ≤ largeCoefficient k ∧
      1 ≤ largeCoefficient k ^ (3 * k) * (16777216 : ℚ) ^ (k - 3) := by
  decide +kernel

private theorem large_head_le {x : ℝ} (hx : 16777216 ≤ x) :
    (∑ k ∈ Icc (3 : ℕ) 8, x ^ (1 / (k : ℝ))) ≤
      (49 / 32 : ℝ) * x ^ (1 / (3 : ℝ)) := by
  have he : (∑ k ∈ Icc 3 8, (largeCoefficient k : ℝ)) = 49 / 32 := by
    norm_num [sum_Icc_succ_top, largeCoefficient]
  rw [← he, sum_mul]
  apply sum_le_sum
  intro k hk
  have hcert := largeCoefficient_certificate k hk
  apply root_ratio_bound (by norm_num : (0 : ℝ) ≤ 16777216) hx
    (Rat.cast_nonneg.mpr hcert.1) (mem_Icc.mp hk).1
  exact_mod_cast hcert.2

private theorem large_log_tail_le {x : ℝ} (hx : 16777216 ≤ x) :
    (Real.log x / Real.log 2) * x ^ (1 / (9 : ℝ)) ≤
      (3 / 5 : ℝ) * x ^ (1 / (3 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hlogB : Real.log (16777216 : ℝ) = 24 * Real.log 2 := by
    rw [show (16777216 : ℝ) = 2 ^ (24 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hdomain : Real.exp ((2 / 9 : ℝ)⁻¹) ≤ 16777216 := by
    rw [← Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 16777216), hlogB]
    have := Real.log_two_gt_d9
    norm_num
    linarith
  have hmono := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 2 / 9)
    hdomain (hdomain.trans hx) hx
  have hroot : (40 : ℝ) ≤ (16777216 : ℝ) ^ (2 / 9 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 16777216)]
    norm_num
  have hquot : Real.log x / x ^ (2 / 9 : ℝ) ≤ (3 / 5 : ℝ) * Real.log 2 := by
    apply hmono.trans
    dsimp only
    rw [hlogB]
    apply (div_le_iff₀ (by positivity : 0 < (16777216 : ℝ) ^ (2 / 9 : ℝ))).mpr
    have h := mul_le_mul_of_nonneg_left hroot
      (by positivity : 0 ≤ (3 / 5 : ℝ) * Real.log 2)
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (div_le_iff₀ (Real.rpow_pos_of_pos hx0 (2 / 9 : ℝ))).mp hquot
  have he : x ^ (2 / 9 : ℝ) * x ^ (1 / 9 : ℝ) = x ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  apply (mul_le_mul_iff_right₀ hlog2).mp
  have hmul := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx0.le (1 / 9 : ℝ))
  calc
    Real.log 2 * ((Real.log x / Real.log 2) * x ^ (1 / (9 : ℝ))) =
        Real.log x * x ^ (1 / (9 : ℝ)) := by field_simp
    _ ≤ (3 / 5 * Real.log 2 * x ^ (2 / 9 : ℝ)) * x ^ (1 / (9 : ℝ)) := hmul
    _ = Real.log 2 * ((3 / 5 : ℝ) * x ^ (1 / (3 : ℝ))) := by
      rw [mul_assoc (3 / 5 * Real.log 2), he]
      ring

private theorem sum_roots_le_head_tail {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    (∑ k ∈ Icc 3 N, x ^ (1 / (k : ℝ))) ≤
      (∑ k ∈ Icc (3 : ℕ) 8, x ^ (1 / (k : ℝ))) + N * x ^ (1 / (9 : ℝ)) := by
  classical
  calc
    _ ≤ ∑ k ∈ Icc 3 N, if k ≤ 8 then x ^ (1 / (k : ℝ))
        else x ^ (1 / (9 : ℝ)) := by
      apply sum_le_sum
      intro k _
      split_ifs with hk
      · rfl
      · apply Real.rpow_le_rpow_of_exponent_le hx
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast (by omega : 9 ≤ k)
    _ = (∑ k ∈ (Icc 3 N).filter (fun k => k ≤ 8), x ^ (1 / (k : ℝ))) +
        ((Icc 3 N).filter (fun k => ¬ k ≤ 8)).card * x ^ (1 / (9 : ℝ)) := by
      rw [sum_ite]
      simp
    _ ≤ _ := by
      apply add_le_add
      · apply sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [mem_filter, mem_Icc] at hk ⊢
          omega
        · intro k _ _
          positivity
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show ((Icc 3 N).filter (fun k => ¬ k ≤ 8)).card ≤ N from
          (card_filter_le _ _).trans (by simp only [Nat.card_Icc]; omega))

theorem elementary_sum_lt_three {x : ℝ} (hx : 16777216 ≤ x) :
    Real.log 4 * (∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊,
      x ^ (1 / (k : ℝ))) < 3 * x ^ (1 / (3 : ℝ)) := by
  have hx1 : 1 ≤ x := by linarith
  have hf := Nat.floor_le (div_nonneg (Real.log_nonneg hx1)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  have hsum := sum_roots_le_head_tail hx1 ⌊Real.log x / Real.log 2⌋₊
  have htail := (mul_le_mul_of_nonneg_right hf
    (Real.rpow_nonneg (by linarith : 0 ≤ x) (1 / (9 : ℝ)))).trans (large_log_tail_le hx)
  have hhead := large_head_le hx
  have hbound : (∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊,
      x ^ (1 / (k : ℝ))) ≤ (341 / 160 : ℝ) * x ^ (1 / (3 : ℝ)) := by
    linarith
  have hlog4 : Real.log 4 < (7 / 5 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    norm_num at *
    linarith
  calc
    _ ≤ Real.log 4 * ((341 / 160 : ℝ) * x ^ (1 / (3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hbound (Real.log_nonneg (by norm_num))
    _ < (7 / 5 : ℝ) * ((341 / 160 : ℝ) * x ^ (1 / (3 : ℝ))) :=
      mul_lt_mul_of_pos_right hlog4 (by positivity)
    _ < _ := by
      have := Real.rpow_pos_of_pos (by linarith : 0 < x) (1 / (3 : ℝ))
      nlinarith

#print axioms root_ratio_bound
#print axioms middle_sum_lt_three
#print axioms elementary_sum_lt_three

end LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections
