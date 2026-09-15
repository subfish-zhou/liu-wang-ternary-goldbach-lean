import LiuWang.Proof.MiddleArcPayment.Continuation.Rightmost

/-! # An elementary pointwise totient bound, not an average over moduli -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.MiddleArcPayment.Continuation

theorem prime_ratio_le_rpow {p : ℕ} (hp : 17 ≤ p) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ (p : ℝ) ^ (1 / 32 : ℝ) := by
  have hpR : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < (p : ℝ) - 1 := by linarith
  have hlog : (2 : ℝ) ≤ Real.log p := by
    have h16 := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by linarith : (16 : ℝ) ≤ p)
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [he] at h16
    linarith [Real.log_two_gt_d9]
  have hsmall : 1 / ((p : ℝ) - 1) ≤ Real.log p / 32 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hp0 hd)
  have he : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by field_simp; ring
  rw [he] at hl
  calc
    _ = Real.exp (Real.log ((p : ℝ) / ((p : ℝ) - 1))) :=
      (Real.exp_log (div_pos hp0 hd)).symm
    _ ≤ Real.exp (Real.log p / 32) := Real.exp_le_exp.mpr (hl.trans hsmall)
    _ = _ := by rw [Real.rpow_def_of_pos hp0]; congr 1; ring

def smallPrimeFactor (p : ℕ) : ℝ :=
  if p < 17 ∧ p.Prime then (p : ℝ) / ((p : ℝ) - 1) else 1

theorem one_le_smallPrimeFactor (p : ℕ) : 1 ≤ smallPrimeFactor p := by
  unfold smallPrimeFactor
  split_ifs with h
  · have hp : (2 : ℝ) ≤ p := by exact_mod_cast h.2.two_le
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  · rfl

theorem smallPrimeFactor_product_le (s : Finset ℕ) :
    (∏ p ∈ s, smallPrimeFactor p) ≤ 6 := by
  have he : (∏ p ∈ s, smallPrimeFactor p) =
      ∏ p ∈ s.filter (fun p => p < 17), smallPrimeFactor p := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hge : ¬ p < 17 := by simpa only [Finset.mem_filter, hp, true_and] using hnot
    simp [smallPrimeFactor, hge]
  rw [he]
  calc
    _ ≤ ∏ p ∈ Finset.range 17, smallPrimeFactor p := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      · intro p _
        exact le_trans (by norm_num) (one_le_smallPrimeFactor p)
      · intro p _ _
        exact one_le_smallPrimeFactor p
    _ ≤ _ := by norm_num [smallPrimeFactor, Finset.prod_range_succ]

theorem totient_ratio_eq_product {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) =
      ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hd : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p h
    have := Nat.prime_of_mem_primeFactors h
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast this.two_le
    linarith
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hp.ne' hd.ne').mpr
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.totient_mul_prod_primeFactors q)
  push_cast at h
  have he : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) =
      ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    simpa using Nat.cast_sub (R := ℝ) (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [he] at h
  nlinarith

theorem totient_ratio_le_six_rpow {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ 6 * (q : ℝ) ^ (1 / 32 : ℝ) := by
  rw [totient_ratio_eq_product hq]
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) :
      (p : ℝ) / ((p : ℝ) - 1) ≤ smallPrimeFactor p * (p : ℝ) ^ (1 / 32 : ℝ) := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    by_cases hs : p < 17
    · rw [smallPrimeFactor, if_pos ⟨hs, hprime⟩]
      apply le_mul_of_one_le_right
      · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · exact Real.one_le_rpow (by exact_mod_cast hprime.one_lt.le) (by norm_num)
    · rw [smallPrimeFactor, if_neg (by tauto), one_mul]
      exact prime_ratio_le_rpow (by omega)
  calc
    _ ≤ ∏ p ∈ q.primeFactors, smallPrimeFactor p * (p : ℝ) ^ (1 / 32 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · exact hlocal
    _ = (∏ p ∈ q.primeFactors, smallPrimeFactor p) *
        (∏ p ∈ q.primeFactors, (p : ℝ)) ^ (1 / 32 : ℝ) := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow]
      intro p _
      positivity
    _ ≤ 6 * (q : ℝ) ^ (1 / 32 : ℝ) := by
      apply mul_le_mul (smallPrimeFactor_product_le _) _ (by positivity) (by norm_num)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

end LiuWang.Proof.MiddleArcPayment.Continuation
