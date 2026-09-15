import LiuWang.Proof.Campaign20260915.Totient.SmallSupport
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Totient

private theorem prod_first_primes_image {M : Type*} [CommMonoid M]
    (k : ℕ) (f : ℕ → M) :
    (∏ p ∈ (Finset.univ : Finset (Fin k)).image (fun i : Fin k => Nat.nth Nat.Prime i), f p) =
      ∏ i : Fin k, f (Nat.nth Nat.Prime i) := by
  apply Finset.prod_image
  intro i _ j _ hij
  exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij)

theorem first_primes_product_monotone :
    Monotone (fun k : ℕ => ∏ i : Fin k, Nat.nth Nat.Prime i) := by
  intro k l hkl
  simp only [Fin.prod_univ_eq_prod_range]
  exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hkl)
    (fun i _ _ => (Nat.prime_nth_prime i).one_lt.le)

theorem first_primes_product_ge_210 {k : ℕ} (hk : 4 ≤ k) :
    210 ≤ ∏ i : Fin k, Nat.nth Nat.Prime i := by
  have h := first_primes_product_monotone hk
  norm_num [Fin.prod_univ_succ] at h
  exact h

theorem totient_ratio_first_primes (k : ℕ) :
    ((∏ i : Fin k, Nat.nth Nat.Prime i : ℕ) : ℝ) /
        ((∏ i : Fin k, Nat.nth Nat.Prime i : ℕ).totient : ℝ) =
      ∏ i : Fin k, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := by
  have hpos : 0 < ∏ i : Fin k, Nat.nth Nat.Prime i :=
    Finset.prod_pos (fun i _ => (Nat.prime_nth_prime i).pos)
  have hsupport : (∏ i : Fin k, Nat.nth Nat.Prime i).primeFactors =
      (Finset.univ : Finset (Fin k)).image (fun i : Fin k => Nat.nth Nat.Prime i) := by
    rw [← prod_first_primes_image k (fun p => p)]
    apply Nat.primeFactors_prod
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.prime_nth_prime i
  rw [LiuWang.Proof.SourceRoute.ThirdArc.Continuation.totient_ratio_product hpos,
    hsupport]
  exact prod_first_primes_image k (fun p => (p : ℝ) / ((p : ℝ) - 1))

theorem original_RS_iff_first_primes :
    (∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) ↔
      (∀ k : ℕ, 4 ≤ k →
        (∏ i : Fin k, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1)) ≤
          nu (∏ i : Fin k, Nat.nth Nat.Prime i : ℕ)) := by
  constructor
  · intro h k hk
    rw [← totient_ratio_first_primes]
    exact h _ (by have := first_primes_product_ge_210 hk; omega)
  · intro h q hq
    by_cases hs : q.primeFactors.card ≤ 3
    · exact totient_ratio_le_nu_of_small_support hq hs
    · have hk : 4 ≤ q.primeFactors.card := by omega
      have hm : ((∏ i : Fin q.primeFactors.card, Nat.nth Nat.Prime i : ℕ) : ℝ) ≤ q := by
        exact_mod_cast first_primes_product_le (show 0 < q by omega)
      have hmin : (27 : ℝ) ≤
          ((∏ i : Fin q.primeFactors.card, Nat.nth Nat.Prime i : ℕ) : ℝ) := by
        have := first_primes_product_ge_210 hk
        exact_mod_cast (show 27 ≤ ∏ i : Fin q.primeFactors.card,
          Nat.nth Nat.Prime i from by omega)
      exact (totient_ratio_le_first_primes (by omega)).trans
        ((h _ hk).trans (nu_monotone_27 hmin (hmin.trans hm) hm))

end LiuWang.Proof.Campaign20260915.Totient
