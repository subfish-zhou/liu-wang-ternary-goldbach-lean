import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.Totient
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.Campaign20260915.Totient

theorem nth_prime_le_ordered_support (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (i : Fin s.card) :
    Nat.nth Nat.Prime i ≤ s.orderEmbOfFin rfl i := by
  have h : ∀ j (hj : j < s.card),
      Nat.nth Nat.Prime j ≤ s.orderEmbOfFin rfl ⟨j, hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      rw [Nat.nth_eq_sInf]
      apply csInf_le (by simp)
      refine ⟨hs _ (s.orderEmbOfFin_mem rfl _), ?_⟩
      intro k hk
      exact (ih k hk (hk.trans hj)).trans_lt
        ((s.orderEmbOfFin rfl).strictMono hk)
  exact h i i.isLt

private theorem prod_ordered_support {M : Type*} [CommMonoid M]
    (s : Finset ℕ) (f : ℕ → M) :
    (∏ p ∈ s, f p) = ∏ i : Fin s.card, f (s.orderEmbOfFin rfl i) := by
  have h := Finset.prod_map (Finset.univ : Finset (Fin s.card))
    (s.orderEmbOfFin rfl).toEmbedding f
  simpa only [Finset.map_orderEmbOfFin_univ, RelEmbedding.coe_toEmbedding] using h

theorem first_primes_product_le {q : ℕ} (hq : 0 < q) :
    (∏ i : Fin q.primeFactors.card, Nat.nth Nat.Prime i) ≤ q := by
  apply le_trans _ (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
  rw [prod_ordered_support q.primeFactors (fun p => p)]
  exact Finset.prod_le_prod' fun i _ =>
    nth_prime_le_ordered_support q.primeFactors
      (fun _ hp => Nat.prime_of_mem_primeFactors hp) i

theorem totient_ratio_le_first_primes {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤
      ∏ i : Fin q.primeFactors.card,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := by
  rw [LiuWang.Proof.SourceRoute.ThirdArc.Continuation.totient_ratio_product hq,
    prod_ordered_support]
  apply Finset.prod_le_prod
  · intro i _
    have hp := Nat.prime_of_mem_primeFactors
      (q.primeFactors.orderEmbOfFin_mem rfl i)
    have hp2 : (2 : ℝ) ≤ q.primeFactors.orderEmbOfFin rfl i := by
      exact_mod_cast hp.two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro i _
    have ha : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by
      exact_mod_cast (Nat.prime_nth_prime i).two_le
    have hab : (Nat.nth Nat.Prime i : ℝ) ≤ q.primeFactors.orderEmbOfFin rfl i := by
      exact_mod_cast nth_prime_le_ordered_support q.primeFactors
        (fun _ hp => Nat.prime_of_mem_primeFactors hp) i
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith

#print axioms nth_prime_le_ordered_support
#print axioms first_primes_product_le
#print axioms totient_ratio_le_first_primes

end LiuWang.Proof.Campaign20260915.Totient
