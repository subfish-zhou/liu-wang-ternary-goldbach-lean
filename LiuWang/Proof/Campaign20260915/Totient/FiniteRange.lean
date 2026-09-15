import LiuWang.Proof.Campaign20260915.Totient.PrefixTable

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section
open scoped BigOperators
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Totient

private theorem primorial_nth {k : ℕ} (hk : 0 < k) :
    primorial (Nat.nth Nat.Prime (k - 1)) =
      ∏ i : Fin k, Nat.nth Nat.Prime i := by
  have hs : Nat.primesLE (Nat.nth Nat.Prime (k - 1)) =
      (Finset.univ : Finset (Fin k)).image (fun i : Fin k => Nat.nth Nat.Prime i) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hle, hp⟩ := Nat.mem_primesLE.mp hp
      have hj : Nat.count Nat.Prime p ≤ k - 1 := by
        apply (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mp
        simpa only [Nat.nth_count hp] using hle
      exact Finset.mem_image.mpr ⟨⟨Nat.count Nat.Prime p, by omega⟩,
        Finset.mem_univ _, Nat.nth_count hp⟩
    · intro hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (by omega),
          Nat.prime_nth_prime i⟩
  rw [primorial_eq_prod_primesLE, hs]
  apply Finset.prod_image
  intro i _ j _ hij
  exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij)

private theorem nth_prime_64 : Nat.nth Nat.Prime 64 = 313 := by
  have hc : Nat.count Nat.Prime 313 = 64 := by decide +kernel
  simpa only [hc] using Nat.nth_count (show Nat.Prime 313 by norm_num)

theorem first_primes_Euler_product_finite {k : ℕ} (hk : 4 ≤ k) (h65 : k ≤ 65) :
    (∏ i : Fin k, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1)) ≤
      nu (∏ i : Fin k, Nat.nth Nat.Prime i : ℕ) := by
  have h7 : 7 ≤ Nat.nth Nat.Prime (k - 1) := by
    have h := (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr
      (show 3 ≤ k - 1 by omega)
    norm_num at h
    exact h
  have h313 : Nat.nth Nat.Prime (k - 1) ≤ 313 := by
    rw [← nth_prime_64]
    exact (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (by omega)
  have h := primorial_RS_of_prime_le_313 (Nat.prime_nth_prime (k - 1)) h7 h313
  rw [primorial_nth (by omega), totient_ratio_first_primes] at h
  exact h

theorem original_RS_of_log_le_294 {q : ℕ} (hq : 3 ≤ q)
    (hlog : Real.log (q : ℝ) ≤ 294) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu q := by
  by_cases hs : q.primeFactors.card ≤ 3
  · exact totient_ratio_le_nu_of_small_support hq hs
  have hk : 4 ≤ q.primeFactors.card := by omega
  have hmin := first_primes_product_ge_210 hk
  have hm := first_primes_product_le (show 0 < q by omega)
  have hbound : q.primeFactors.card < 65 := by
    by_contra! h65
    have hprod : primorial 313 ≤ q := by
      have ht := (first_primes_product_monotone h65).trans hm
      dsimp only at ht
      have he := primorial_nth (show 0 < (65 : ℕ) by norm_num)
      norm_num only [show (65 - 1 : ℕ) = 64 by norm_num, nth_prime_64] at he
      rwa [← he] at ht
    have hp : (0 : ℝ) < primorial 313 := by
      exact_mod_cast (show 0 < primorial 313 from
        Finset.prod_pos (fun p hp => (Nat.mem_primesLE.mp hp).2.pos))
    have hl := Real.log_le_log hp (show (primorial 313 : ℝ) ≤ q by exact_mod_cast hprod)
    have ht := theta_313_gt_294
    rw [Chebyshev.theta_eq_log_primorial] at ht
    norm_num only [Nat.floor_ofNat] at ht
    linarith
  have hmr : ((∏ i : Fin q.primeFactors.card, Nat.nth Nat.Prime i : ℕ) : ℝ) ≤ q := by
    exact_mod_cast hm
  have h27 : (27 : ℝ) ≤
      ((∏ i : Fin q.primeFactors.card, Nat.nth Nat.Prime i : ℕ) : ℝ) := by
    exact_mod_cast (show 27 ≤ ∏ i : Fin q.primeFactors.card, Nat.nth Nat.Prime i by omega)
  exact (totient_ratio_le_first_primes (by omega)).trans
    ((first_primes_Euler_product_finite hk (by omega)).trans
      (nu_monotone_27 h27 (h27.trans hmr) hmr))

theorem original_RS_exception_223092870 :
    (223092870 : ℝ) / ((223092870 : ℕ).totient : ℝ) ≤ nu 223092870 := by
  have he : primorial 23 = 223092870 := by decide +kernel
  simpa only [he, Nat.cast_ofNat] using
    primorial_RS_of_prime_le_313 (show Nat.Prime 23 by norm_num)
      (by norm_num) (by norm_num)

#print axioms first_primes_Euler_product_finite
#print axioms original_RS_of_log_le_294
#print axioms original_RS_exception_223092870

end LiuWang.Proof.Campaign20260915.Totient
