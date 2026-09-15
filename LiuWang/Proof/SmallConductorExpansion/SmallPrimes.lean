import LiuWang.Proof.SmallConductorExpansion.PrimeTables

/-! # Exhaustive quadratic-character coverage at the odd primes up to 31 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def smallPrimes : Finset ℕ := {7, 11, 13, 17, 19, 23, 29, 31}

def smallPrimeValues : ℕ → List ℤ
  | 7 => [0, 1, 1, -1, 1, -1, -1]
  | 11 => [0, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1]
  | 13 => [0, 1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 1]
  | 17 => [0, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, -1, 1, 1]
  | 19 => [0, 1, -1, -1, 1, 1, 1, 1, -1, 1, -1, 1, -1, -1, -1, -1, 1, 1, -1]
  | 23 => [0, 1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, -1, -1, -1]
  | 29 => [0, 1, -1, -1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1, 1, -1, -1, 1]
  | 31 => [0, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1]
  | _ => []

def smallPrimeAmplitude : ℕ → ℚ
  | 7 | 13 | 17 => 2
  | 11 | 19 | 29 => 3
  | 23 => 5
  | 31 => 6
  | _ => 0

theorem smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by decide

theorem smallPrime_table (p : ℕ) (hp : p ∈ smallPrimes) [Fact p.Prime] :
    ∀ a : ZMod p, primeCharacter p a = ((smallPrimeValues p).getD a.val 0 : ℂ) := by
  apply primeCharacter_table
  fin_cases hp <;> decide +revert

theorem certificate_seven :
    RationalCertificate 7 (smallPrimeValues 7) 32 (smallPrimeAmplitude 7) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem certificate_eleven :
    RationalCertificate 11 (smallPrimeValues 11) 32 (smallPrimeAmplitude 11) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem certificate_thirteen :
    RationalCertificate 13 (smallPrimeValues 13) 32 (smallPrimeAmplitude 13) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem certificate_seventeen :
    RationalCertificate 17 (smallPrimeValues 17) 32 (smallPrimeAmplitude 17) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem certificate_nineteen :
    RationalCertificate 19 (smallPrimeValues 19) 32 (smallPrimeAmplitude 19) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem certificate_twentythree :
    RationalCertificate 23 (smallPrimeValues 23) 32 (smallPrimeAmplitude 23) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem certificate_twentynine :
    RationalCertificate 29 (smallPrimeValues 29) 32 (smallPrimeAmplitude 29) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem certificate_thirtyone :
    RationalCertificate 31 (smallPrimeValues 31) 32 (smallPrimeAmplitude 31) (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, smallPrimeValues, smallPrimeAmplitude, Finset.sum_range_succ]

theorem smallPrime_certificate (p : ℕ) (hp : p ∈ smallPrimes) :
    RationalCertificate p (smallPrimeValues p) 32 (smallPrimeAmplitude p) (6 / 5) := by
  fin_cases hp
  · exact certificate_seven
  · exact certificate_eleven
  · exact certificate_thirteen
  · exact certificate_seventeen
  · exact certificate_nineteen
  · exact certificate_twentythree
  · exact certificate_twentynine
  · exact certificate_thirtyone

theorem smallPrime_original_region (p : ℕ) [NeZero p] (hp : p ∈ smallPrimes)
    (chi : DirichletCharacter ℂ p) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have : Fact p.Prime := ⟨smallPrimes_prime p hp⟩
  have hp2 : p ≠ 2 := by fin_cases hp <;> decide
  rw [quadratic_prime_eq p hp2 chi hc hsq]
  exact rationalCertificate_original_region (primeCharacter p) (primeCharacter_ne_one p hp2)
    (smallPrimeValues p) (smallPrime_table p hp)
    (by decide) (by decide) (smallPrime_certificate p hp) hx hb

end LiuWang.Proof.SmallConductorExpansion
