import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.TailKernel

/-! Uniform finite right-tail means, with both oscillatory directions included. -/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem finite_power_sum (S : Finset ℕ) {σ : ℝ} (hσ : 1 < σ) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) :=
  (Summable.sum_le_tsum S (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.summable_nat_rpow.mpr (by linarith))).trans
    (AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le σ hσ)

theorem finite_log_moment (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    {σ : ℝ} (hσ : 1 < σ) :
    (∑ n ∈ S, (n : ℝ) ^ (1 - 2 * σ) * (3 + Real.log n)) ≤
      3 * (1 + 1 / (2 * σ - 2)) + (1 / (σ - 1)) * (1 + 1 / (σ - 1)) := by
  have hterm (n : ℕ) (hn : n ∈ S) :
      (n : ℝ) ^ (1 - 2 * σ) * (3 + Real.log n) ≤
        3 * (n : ℝ) ^ (-(2 * σ - 1)) + (1 / (σ - 1)) * (n : ℝ) ^ (-σ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hS n hn
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_rpow_div hn0.le (by linarith : 0 < σ - 1))
      (Real.rpow_nonneg hn0.le (1 - 2 * σ))
    have he : (n : ℝ) ^ (1 - 2 * σ) * ((n : ℝ) ^ (σ - 1) / (σ - 1)) =
        (1 / (σ - 1)) * (n : ℝ) ^ (-σ) := by
      rw [← mul_div_assoc, ← Real.rpow_add hn0]
      rw [show 1 - 2 * σ + (σ - 1) = -σ by ring]
      ring
    rw [he] at h
    rw [show -(2 * σ - 1) = 1 - 2 * σ by ring]
    nlinarith
  have hs := sum_le_sum hterm
  simp only [sum_add_distrib, ← mul_sum] at hs
  have h1 := finite_power_sum S (by linarith : 1 < 2 * σ - 1)
  have h2 := mul_le_mul_of_nonneg_left (finite_power_sum S hσ)
    (by positivity : 0 ≤ 1 / (σ - 1))
  rw [show 2 * σ - 1 - 1 = 2 * σ - 2 by ring] at h1
  linarith

theorem kernel_sum_erase_eq (S : Finset ℕ) (σ : ℝ) :
    (∑ m ∈ S, ∑ n ∈ S.erase m, tailKernel σ m n) =
      2 * ∑ m ∈ S, ∑ n ∈ S.filter (fun n => m < n), tailKernel σ m n := by
  have hrow (m : ℕ) (hm : m ∈ S) :
      (∑ n ∈ S.erase m, tailKernel σ m n) = ∑ n ∈ S, tailKernel σ m n := by
    rw [← sum_erase_add _ _ hm]
    simp [tailKernel]
  rw [sum_congr rfl hrow]
  have hterm (m n : ℕ) : tailKernel σ m n =
      (if m < n then tailKernel σ m n else 0) +
        (if n < m then tailKernel σ n m else 0) := by
    rcases lt_trichotomy m n with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst n; simp [tailKernel]
    · simp [h, not_lt_of_ge h.le, tailKernel_symm σ m n]
  have hexpand : (∑ m ∈ S, ∑ n ∈ S, tailKernel σ m n) =
      ∑ m ∈ S, ∑ n ∈ S, ((if m < n then tailKernel σ m n else 0) +
        (if n < m then tailKernel σ n m else 0)) :=
    sum_congr rfl (fun m _ => sum_congr rfl (fun n _ => hterm m n))
  rw [hexpand]
  simp only [sum_add_distrib]
  have hswap :
      (∑ m ∈ S, ∑ n ∈ S, if n < m then tailKernel σ n m else 0) =
        ∑ m ∈ S, ∑ n ∈ S, if m < n then tailKernel σ m n else 0 := sum_comm
  rw [hswap]
  simp only [sum_filter]
  ring

theorem finite_kernel_bound (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    {σ : ℝ} (hσ : 1 < σ) :
    (∑ m ∈ S, ∑ n ∈ S.erase m, tailKernel σ m n) ≤
      4 * (3 * (1 + 1 / (2 * σ - 2)) +
        (1 / (σ - 1)) * (1 + 1 / (σ - 1))) +
      4 * (1 + 1 / (σ - 1)) ^ 2 := by
  rw [kernel_sum_erase_eq]
  have hsum := sum_le_sum (fun m hm => kernel_row_bound S hσ (hS m hm))
  simp only [sum_add_distrib, mul_assoc, ← mul_sum, ← sum_mul] at hsum
  have hm := finite_log_moment S hS hσ
  have hp := finite_power_sum S hσ
  have hp0 : 0 ≤ ∑ n ∈ S, (n : ℝ) ^ (-σ) := sum_nonneg (fun n _ => by positivity)
  nlinarith

theorem finite_tail_diagonal {S : Finset ℕ} {N : ℕ} (hN : 2 ≤ N)
    (hS : ∀ n ∈ S, N ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    (∑ n ∈ S, ((n : ℝ) ^ (-σ)) ^ 2) ≤ 1 / ((N : ℝ) - 1) := by
  have hterm (n : ℕ) (hn : n ∈ S) :
      ((n : ℝ) ^ (-σ)) ^ 2 ≤ (n : ℝ) ^ (-(2 : ℝ)) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := hS n hn; omega)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  have heq : (∑ n ∈ S, (n : ℝ) ^ (-(2 : ℝ))) =
      ∑ k ∈ S.image (fun n => n - N), ((k + N : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    rw [sum_image (fun a ha b hb hab => by have := hS a ha; have := hS b hb; omega)]
    apply sum_congr rfl
    intro n hn
    rw [Nat.sub_add_cancel (hS n hn)]
  have hsum : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
    (summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  have hb := hsum.sum_le_tsum (S.image (fun n => n - N)) (fun _ _ => by positivity)
  have ht := rpow_tail_le (by norm_num : (1 : ℝ) < 2) hN
  have hh := sum_le_sum hterm
  rw [heq] at hh
  have he : ((N : ℝ) - 1) ^ (1 - (2 : ℝ)) / (2 - 1) = 1 / ((N : ℝ) - 1) := by
    norm_num [Real.rpow_neg_one]
  rw [he] at ht
  exact hh.trans (hb.trans ht)

theorem finite_tail_mean {S : Finset ℕ} {N : ℕ} (hN : 2 ≤ N)
    (hS : ∀ n ∈ S, N ≤ n) {σ : ℝ} (hσ : 1 < σ)
    {a : ℕ → ℂ} (ha : ∀ n ∈ S, ‖a n‖ ≤ (n : ℝ) ^ (-σ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖exponentialPolynomial S a (fun n => -Real.log n) t‖ ^ 2) ≤
      2 * T / ((N : ℝ) - 1) +
      8 * (3 * (1 + 1 / (2 * σ - 2)) +
        (1 / (σ - 1)) * (1 + 1 / (σ - 1))) +
      8 * (1 + 1 / (σ - 1)) ^ 2 := by
  have hpos (n : ℕ) (hn : n ∈ S) : 0 < n := by have := hS n hn; omega
  have hw : Set.InjOn (fun n : ℕ => -Real.log n) S := by
    intro m hm n hn he
    have he' : Real.log m = Real.log n := neg_injective he
    have hlog := Real.log_injOn_pos
      (show (m : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < m; exact_mod_cast hpos m hm)
      (show (n : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < n; exact_mod_cast hpos n hn) he'
    exact_mod_cast hlog
  have hmean := finite_mean_le S a (fun n => -Real.log n) hw hT
  have hd := finite_tail_diagonal hN hS hσ
  have had := sum_le_sum (fun n hn => pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2)
  have ho : (∑ m ∈ S, ∑ n ∈ S.erase m,
      ‖a m‖ * ‖a n‖ / |-Real.log m - -Real.log n|) ≤
      ∑ m ∈ S, ∑ n ∈ S.erase m, tailKernel σ m n := by
    apply sum_le_sum
    intro m hm
    apply sum_le_sum
    intro n hn
    have hmul := mul_le_mul (ha m hm) (ha n (mem_erase.mp hn).2)
      (norm_nonneg _) (by positivity)
    have he : |-Real.log m - -Real.log n| = |Real.log m - Real.log n| := by
      rw [neg_sub_neg, abs_sub_comm]
    rw [he]
    exact div_le_div_of_nonneg_right hmul (abs_nonneg _)
  have hk := finite_kernel_bound S hpos hσ
  have hdiag := mul_le_mul_of_nonneg_left (had.trans hd) (by positivity : 0 ≤ 2 * T)
  rw [mul_one_div] at hdiag
  linarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
