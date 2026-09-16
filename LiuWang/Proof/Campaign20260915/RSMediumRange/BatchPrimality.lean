import LiuWang.Proof.Campaign20260915.RSMediumRange.CertificateSoundness
import Mathlib.Data.Nat.Prime.Factorial

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem coprime_of_mul_add_one {a b u v : ℕ} (h : a * u + 1 = b * v) :
    Nat.Coprime a b := by
  have ha : Nat.gcd a b ∣ a * u := dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) u
  have hb : Nat.gcd a b ∣ a * u + 1 := by
    rw [h]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) v
  have h1 : Nat.gcd a b ∣ 1 := (Nat.dvd_add_iff_right ha).mpr hb
  exact Nat.dvd_one.mp h1

theorem prime_of_coprime_factorial {p : ℕ} (hp : 2 ≤ p) (hb : p ≤ 100000000)
    (hc : Nat.Coprime p (Nat.factorial 10000)) : p.Prime := by
  by_contra hn
  have hmin := Nat.minFac_prime (n := p) (by omega)
  have hs := Nat.minFac_sq_le_self (by omega : 0 < p) hn
  have hsmall : p.minFac ≤ 10000 := by nlinarith
  have he := Nat.eq_one_of_dvd_coprimes hc (Nat.minFac_dvd p)
    (Nat.dvd_factorial hmin.pos hsmall)
  exact hmin.ne_one he

theorem batch_prime_of_coprime_factorial {ps : List ℕ}
    (hb : ∀ p ∈ ps, 2 ≤ p ∧ p ≤ 100000000)
    (hc : Nat.Coprime ps.prod (Nat.factorial 10000)) :
    ∀ p ∈ ps, p.Prime := by
  intro p hp
  exact prime_of_coprime_factorial (hb p hp).1 (hb p hp).2
    (Nat.Coprime.of_dvd_left (List.dvd_prod hp) hc)

#print axioms batch_prime_of_coprime_factorial

end LiuWang.Proof.Campaign20260915.RSMediumRange
