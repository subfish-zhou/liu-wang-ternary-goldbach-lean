import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.Totient

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def endpointPrimeCorrection (p : ℕ) : ℝ :=
  if p < 23 ∧ p.Prime then max 1 ((p : ℝ) ^ 59 / ((p : ℝ) - 1) ^ 60) else 1

def endpointTotientConstant : ℝ := ∏ p ∈ Finset.range 23, endpointPrimeCorrection p

theorem one_le_endpointPrimeCorrection (p : ℕ) : 1 ≤ endpointPrimeCorrection p := by
  unfold endpointPrimeCorrection
  split_ifs
  · exact le_max_left _ _
  · rfl

theorem endpoint_large_prime_ratio {p : ℕ} (hp : 23 ≤ p) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ (p : ℝ) ^ (1 / 60 : ℝ) := by
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < (p : ℝ) - 1 := by linarith
  have hlog : (11 / 4 : ℝ) ≤ Real.log p := by
    have h16 := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
      (by linarith : (16 : ℝ) ≤ p)
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at h16
    norm_num only [Nat.cast_ofNat] at h16
    linarith [Real.log_two_gt_d9]
  have hsmall : 1 / ((p : ℝ) - 1) ≤ Real.log p / 60 := by
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
    _ ≤ Real.exp (Real.log p / 60) := Real.exp_le_exp.mpr (hl.trans hsmall)
    _ = _ := by rw [Real.rpow_def_of_pos hp0]; congr 1; ring

theorem endpoint_prime_ratio_power {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) / ((p : ℝ) - 1)) ^ 60 ≤ endpointPrimeCorrection p * p := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hd : 0 < (p : ℝ) - 1 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  by_cases hs : p < 23
  · rw [endpointPrimeCorrection, if_pos ⟨hs, hp⟩]
    calc
      _ = ((p : ℝ) ^ 59 / ((p : ℝ) - 1) ^ 60) * p := by
        rw [div_pow, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hp0.le
  · rw [endpointPrimeCorrection, if_neg (by tauto), one_mul]
    have h := pow_le_pow_left₀ (div_nonneg hp0.le hd.le) (endpoint_large_prime_ratio (by omega)) 60
    rw [← Real.rpow_mul_natCast hp0.le] at h
    norm_num at h
    exact h

theorem endpoint_correction_product_le (s : Finset ℕ) :
    (∏ p ∈ s, endpointPrimeCorrection p) ≤ endpointTotientConstant := by
  have he : (∏ p ∈ s, endpointPrimeCorrection p) =
      ∏ p ∈ s.filter (fun p => p < 23), endpointPrimeCorrection p := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hn : ¬p < 23 := by simpa only [Finset.mem_filter, hp, true_and] using hnot
    simp [endpointPrimeCorrection, hn]
  rw [he]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  · intro p _
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_endpointPrimeCorrection p)
  · intro p _ _
    exact one_le_endpointPrimeCorrection p

theorem endpoint_totient_power_bound {q : ℕ} (hq : 0 < q) :
    (q : ℝ) ^ 59 ≤ endpointTotientConstant * (q.totient : ℝ) ^ 60 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hC : 0 ≤ endpointTotientConstant :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans (by
      simpa using endpoint_correction_product_le (∅ : Finset ℕ))
  have h : ((q : ℝ) / q.totient) ^ 60 ≤ endpointTotientConstant * q := by
    rw [SourceRoute.ThirdArc.Continuation.totient_ratio_product hq, ← Finset.prod_pow]
    calc
      _ ≤ ∏ p ∈ q.primeFactors, endpointPrimeCorrection p * p := by
        apply Finset.prod_le_prod
        · intro p _
          positivity
        · intro p hp
          exact endpoint_prime_ratio_power (Nat.prime_of_mem_primeFactors hp)
      _ = (∏ p ∈ q.primeFactors, endpointPrimeCorrection p) * ∏ p ∈ q.primeFactors, (p : ℝ) :=
        Finset.prod_mul_distrib
      _ ≤ endpointTotientConstant * q := by
        apply mul_le_mul (endpoint_correction_product_le _) _ (by positivity) hC
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  rw [div_pow] at h
  have h := (div_le_iff₀ (pow_pos hf 60)).mp h
  apply le_of_mul_le_mul_left (a := (q : ℝ)) ?_ hq0
  convert h using 1 <;> ring

theorem endpoint_totient_fixed_certificate :
    endpointTotientConstant ≤ (4.4772 : ℝ) ^ 60 := by
  norm_num [endpointTotientConstant, endpointPrimeCorrection, Finset.prod_range_succ]

theorem endpoint_totient_bound {q : ℕ} (hq : 0 < q) :
    (q : ℝ) ^ (59 / 60 : ℝ) / q.totient ≤ 4.4772 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : 60 ≠ 0)).mp
  have hs : ((q : ℝ) ^ (59 / 60 : ℝ)) ^ (60 : ℕ) = (q : ℝ) ^ (59 : ℕ) := by
    rw [← Real.rpow_mul_natCast hq0.le]
    norm_num
  rw [div_pow, hs]
  apply (div_le_iff₀ (pow_pos hf 60)).mpr
  exact (endpoint_totient_power_bound hq).trans
    (mul_le_mul_of_nonneg_right endpoint_totient_fixed_certificate (by positivity))

#print axioms endpoint_totient_fixed_certificate
#print axioms endpoint_totient_bound

end LiuWang.Proof.Campaign20260915.SecondTerminal
