import LiuWang.Proof.Campaign20260915.Totient.PrimorialReduction
import LiuWang.Proof.Campaign20260915.Totient.PrefixTable

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.Campaign20260915.Totient

theorem primesLE_eq_first_primes (n : ℕ) :
    Nat.primesLE n =
      (Finset.univ : Finset (Fin (Nat.primesLE n).card)).image
        (fun i : Fin (Nat.primesLE n).card => Nat.nth Nat.Prime i) := by
  have hc : (Nat.primesLE n).card = Nat.count Nat.Prime (n + 1) :=
    Nat.primesLE_card_eq_primeCounting n
  ext p
  constructor
  · intro hp
    obtain ⟨hpn, hp⟩ := Nat.mem_primesLE.mp hp
    have hj : Nat.count Nat.Prime p < (Nat.primesLE n).card := by
      rw [hc]
      apply (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mpr
      simpa only [Nat.nth_count hp] using (show p < n + 1 by omega)
    exact Finset.mem_image.mpr ⟨⟨Nat.count Nat.Prime p, hj⟩, Finset.mem_univ _,
      Nat.nth_count hp⟩
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hi : (i : ℕ) < Nat.count Nat.Prime (n + 1) := by rw [← hc]; exact i.isLt
    exact Nat.mem_primesLE.mpr ⟨by have := Nat.nth_lt_of_lt_count hi; omega,
      Nat.prime_nth_prime i⟩

theorem primorial_eq_first_primes (n : ℕ) :
    primorial n = ∏ i : Fin (Nat.primesLE n).card, Nat.nth Nat.Prime i := by
  conv_lhs => rw [primorial_eq_prod_primesLE, primesLE_eq_first_primes]
  apply Finset.prod_image (f := fun p : ℕ => p)
  intro i _ j _ hij
  exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij)

theorem theorem33_totient_cutoff {q : ℕ} {x : ℝ} (hq : 0 < q)
    (hx : 5 ≤ x) (ht : Real.log (q : ℝ) < Chebyshev.theta x) :
    (q : ℝ) / (q.totient : ℝ) ≤ (prefixEuler ⌊x - 2⌋₊ : ℝ) := by
  let m := (Nat.primesLE ⌊x⌋₊).card
  let k := q.primeFactors.card
  have hkm : k < m := by
    by_contra! hmk
    have hp : primorial ⌊x⌋₊ ≤ q := by
      rw [primorial_eq_first_primes]
      exact (first_primes_product_monotone hmk).trans (first_primes_product_le hq)
    have hpR : (primorial ⌊x⌋₊ : ℝ) ≤ q := by exact_mod_cast hp
    have hh := Real.log_le_log (by exact_mod_cast primorial_pos ⌊x⌋₊) hpR
    rw [Chebyshev.theta_eq_log_primorial] at ht
    linarith
  have hm3 : 3 ≤ m := by
    have hs : Nat.primesLE 5 ⊆ Nat.primesLE ⌊x⌋₊ := by
      intro p hp
      obtain ⟨hpn, hp⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpn.trans ((Nat.le_floor_iff (by linarith)).mpr hx), hp⟩
    have h := Finset.card_le_card hs
    have h3 : (Nat.primesLE 5).card = 3 := by decide +kernel
    rwa [h3] at h
  have hlast : (Nat.nth Nat.Prime (m - 1) : ℝ) ≤ x := by
    have hc : m = Nat.count Nat.Prime (⌊x⌋₊ + 1) := Nat.primesLE_card_eq_primeCounting _
    have hp : Nat.nth Nat.Prime (m - 1) ≤ ⌊x⌋₊ := by
      have hh := Nat.nth_lt_of_lt_count (show m - 1 < Nat.count Nat.Prime (⌊x⌋₊ + 1) by omega)
      omega
    have hpR : (Nat.nth Nat.Prime (m - 1) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hp
    exact hpR.trans (Nat.floor_le (by linarith))
  have hsub : (Finset.univ : Finset (Fin k)).image (fun i : Fin k => Nat.nth Nat.Prime i) ⊆
      Nat.primesLE ⌊x - 2⌋₊ := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hij : (i : ℕ) < m - 1 := by omega
    have hpq := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) hij
    change Nat.nth Nat.Prime i < Nat.nth Nat.Prime (m - 1) at hpq
    have hbig : 5 ≤ Nat.nth Nat.Prime (m - 1) := by
      have h := (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (show 2 ≤ m - 1 by omega)
      simpa only [Nat.nth_prime_two_eq_five] using h
    have hgap : Nat.nth Nat.Prime i + 2 ≤ Nat.nth Nat.Prime (m - 1) := by
      have hi2 := (Nat.prime_nth_prime i).eq_two_or_odd
      have hj2 := (Nat.prime_nth_prime (m - 1)).eq_two_or_odd
      omega
    have hpr : (Nat.nth Nat.Prime i : ℝ) ≤ x - 2 := by
      have hg : (Nat.nth Nat.Prime i : ℝ) + 2 ≤ Nat.nth Nat.Prime (m - 1) := by
        exact_mod_cast hgap
      linarith
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff (by linarith)).mpr hpr, Nat.prime_nth_prime i⟩
  have hprod :
      (∏ i : Fin k, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1)) =
      ∏ p ∈ (Finset.univ : Finset (Fin k)).image (fun i : Fin k => Nat.nth Nat.Prime i),
        (p : ℝ) / (p - 1) := by
    symm
    apply Finset.prod_image
    intro i _ j _ hij
    exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij)
  apply (totient_ratio_le_first_primes hq).trans
  rw [hprod]
  unfold prefixEuler
  push_cast
  apply Finset.prod_le_prod_of_subset_of_one_le hsub
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    exact (le_div_iff₀ (by linarith)).mpr (by linarith)

#print axioms theorem33_totient_cutoff

end LiuWang.Proof.Campaign20260915.Totient
