import LiuWang.Proof.SourceRoute.ThirdArc.ErrorBudget

/-! Exact small-prime corrections in an elementary pointwise totient bound. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

def primeCorrection (p : ℕ) : ℝ :=
  if p < 43 ∧ p.Prime then max 1 ((p : ℝ) ^ 127 / ((p : ℝ) - 1) ^ 128) else 1

def totientConstant : ℝ := ∏ p ∈ Finset.range 43, primeCorrection p

theorem one_le_primeCorrection (p : ℕ) : 1 ≤ primeCorrection p := by
  unfold primeCorrection
  split_ifs
  · exact le_max_left _ _
  · rfl

theorem large_prime_ratio {p : ℕ} (hp : 43 ≤ p) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ (p : ℝ) ^ (1 / 128 : ℝ) := by
  have hpR : (43 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < (p : ℝ) - 1 := by linarith
  have hlog : (16 / 5 : ℝ) ≤ Real.log p := by
    have h32 := Real.log_le_log (by norm_num : (0 : ℝ) < 32)
      (by linarith : (32 : ℝ) ≤ p)
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at h32
    norm_num only [Nat.cast_ofNat] at h32
    linarith [Real.log_two_gt_d9]
  have hsmall : 1 / ((p : ℝ) - 1) ≤ Real.log p / 128 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hp0 hd)
  have he : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
    field_simp
    ring
  rw [he] at hl
  calc
    _ = Real.exp (Real.log ((p : ℝ) / ((p : ℝ) - 1))) :=
      (Real.exp_log (div_pos hp0 hd)).symm
    _ ≤ Real.exp (Real.log p / 128) := Real.exp_le_exp.mpr (hl.trans hsmall)
    _ = _ := by rw [Real.rpow_def_of_pos hp0]; congr 1; ring

theorem prime_ratio_power {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) / ((p : ℝ) - 1)) ^ 128 ≤ primeCorrection p * p := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hd : 0 < (p : ℝ) - 1 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  by_cases hs : p < 43
  · rw [primeCorrection, if_pos ⟨hs, hp⟩]
    calc
      _ = ((p : ℝ) ^ 127 / ((p : ℝ) - 1) ^ 128) * p := by
        rw [div_pow, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hp0.le
  · rw [primeCorrection, if_neg (by tauto), one_mul]
    have h := pow_le_pow_left₀ (div_nonneg hp0.le hd.le) (large_prime_ratio (by omega)) 128
    rw [← Real.rpow_mul_natCast hp0.le] at h
    norm_num at h
    exact h

theorem correction_product_le (s : Finset ℕ) :
    (∏ p ∈ s, primeCorrection p) ≤ totientConstant := by
  have he : (∏ p ∈ s, primeCorrection p) =
      ∏ p ∈ s.filter (fun p => p < 43), primeCorrection p := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hn : ¬p < 43 := by simpa only [Finset.mem_filter, hp, true_and] using hnot
    simp [primeCorrection, hn]
  rw [he]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  · intro p _
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_primeCorrection p)
  · intro p _ _
    exact one_le_primeCorrection p

theorem totient_ratio_product {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) =
      ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hd : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p h
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors h).two_le
    linarith
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hp.ne' hd.ne').mpr
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.totient_mul_prod_primeFactors q)
  push_cast at h
  have he : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) =
      ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    simpa only [Nat.cast_one] using
      Nat.cast_sub (R := ℝ) (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [he] at h
  nlinarith

theorem totient_power_bound {q : ℕ} (hq : 0 < q) :
    (q : ℝ) ^ 127 ≤ totientConstant * (q.totient : ℝ) ^ 128 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hC : 0 ≤ totientConstant :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans (by
      simpa using correction_product_le (∅ : Finset ℕ))
  have h : ((q : ℝ) / q.totient) ^ 128 ≤ totientConstant * q := by
    rw [totient_ratio_product hq, ← Finset.prod_pow]
    calc
      _ ≤ ∏ p ∈ q.primeFactors, primeCorrection p * p := by
        apply Finset.prod_le_prod
        · intro p _
          positivity
        · intro p hp
          exact prime_ratio_power (Nat.prime_of_mem_primeFactors hp)
      _ = (∏ p ∈ q.primeFactors, primeCorrection p) * ∏ p ∈ q.primeFactors, (p : ℝ) :=
        Finset.prod_mul_distrib
      _ ≤ totientConstant * q := by
        apply mul_le_mul (correction_product_le _) _ (by positivity) hC
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  rw [div_pow] at h
  have h := (div_le_iff₀ (pow_pos hf 128)).mp h
  apply le_of_mul_le_mul_left (a := (q : ℝ)) ?_ hq0
  convert h using 1 <;> ring

theorem totient_endpoint_certificates :
    totientConstant ≤ (0.00000068 : ℝ) ^ 128 * 3100 ^ 253 ∧
      totientConstant ≤ (0.11585 : ℝ) ^ 128 * 3100 ^ 61 := by
  norm_num [totientConstant, primeCorrection, Finset.prod_range_succ]

theorem principal_totient_scale {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    sourceL N ≤ 0.00000068 * (q.totient : ℝ) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : 0 < q := Nat.cast_pos.mp ((sourceP_pos
    (exp_2000_le_of_exp_3100_le hN)).trans_le hq)
  have hC : totientConstant ≤ (0.00000068 : ℝ) ^ 128 * sourceL N ^ 253 :=
    totient_endpoint_certificates.1.trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 253) (by positivity))
  apply (pow_le_pow_iff_left₀ hL.le (by positivity) (by norm_num : 128 ≠ 0)).mp
  apply le_of_mul_le_mul_left (a := sourceL N ^ 253) ?_ (pow_pos hL 253)
  calc
    _ = (sourceL N ^ 3) ^ 127 := by ring
    _ ≤ (q : ℝ) ^ 127 := pow_le_pow_left₀ (pow_nonneg hL.le 3) hq 127
    _ ≤ totientConstant * (q.totient : ℝ) ^ 128 := totient_power_bound hq0
    _ ≤ ((0.00000068 : ℝ) ^ 128 * sourceL N ^ 253) * (q.totient : ℝ) ^ 128 :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by ring

theorem single_zero_totient_scale {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    sourceL N * Real.sqrt q ≤ 0.11585 * (q.totient : ℝ) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : 0 < q := Nat.cast_pos.mp ((sourceP_pos
    (exp_2000_le_of_exp_3100_le hN)).trans_le hq)
  have hC : totientConstant ≤ (0.11585 : ℝ) ^ 128 * sourceL N ^ 61 :=
    totient_endpoint_certificates.2.trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 61) (by positivity))
  have hs : (Real.sqrt (q : ℝ)) ^ 128 = (q : ℝ) ^ 64 := by
    rw [show (128 : ℕ) = 2 * 64 by norm_num, pow_mul, Real.sq_sqrt (Nat.cast_nonneg q)]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 128 ≠ 0)).mp
  apply le_of_mul_le_mul_left (a := sourceL N ^ 61) ?_ (pow_pos hL 61)
  calc
    _ = (sourceL N ^ 3) ^ 63 * (q : ℝ) ^ 64 := by rw [mul_pow, hs]; ring
    _ ≤ (q : ℝ) ^ 63 * (q : ℝ) ^ 64 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg hL.le 3) hq 63) (by positivity)
    _ = (q : ℝ) ^ 127 := by ring
    _ ≤ totientConstant * (q.totient : ℝ) ^ 128 := totient_power_bound hq0
    _ ≤ ((0.11585 : ℝ) ^ 128 * sourceL N ^ 61) * (q.totient : ℝ) ^ 128 :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by ring

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
