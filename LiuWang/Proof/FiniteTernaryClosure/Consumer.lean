import LiuWang.Proof.FiniteTernaryClosure.Analytic

set_option autoImplicit false

namespace LiuWang.Proof.FiniteTernaryClosure

theorem excludes_one : ¬LiuWang.IsThreeOddPrimeSum 1 :=
  not_isThreeOddPrimeSum_of_lt_nine (by decide)

theorem excludes_five : ¬LiuWang.IsThreeOddPrimeSum 5 :=
  not_isThreeOddPrimeSum_of_lt_nine (by decide)

theorem excludes_seven : ¬LiuWang.IsThreeOddPrimeSum 7 :=
  not_isThreeOddPrimeSum_of_lt_nine (by decide)

theorem seven_is_three_primes : (2 : ℕ).Prime ∧ (3 : ℕ).Prime ∧ 7 = 2 + 2 + 3 := by
  norm_num

example : checkCertificate ⟨7, 2, 2, 3⟩ = false := by decide
example : checkCertificate ⟨9, 1, 3, 5⟩ = false := by decide
example : checkCertificate ⟨15, 3, 3, 9⟩ = false := by decide
example : checkCertificate ⟨11, 3, 3, 3⟩ = false := by decide
example : checkCertificate ⟨9, 3, 3, 3⟩ = true := by decide

example : checkInterval 9 10 [⟨9, 3, 3, 3⟩] = true := by decide
example : checkInterval 9 12 [⟨9, 3, 3, 3⟩] = false := by decide
example : checkInterval 9 12 [⟨9, 3, 3, 3⟩, ⟨9, 3, 3, 3⟩] = false := by decide
example : checkInterval 9 12 [⟨11, 3, 3, 5⟩, ⟨9, 3, 3, 3⟩] = false := by decide
example : checkInterval 9 10 [⟨9, 3, 3, 3⟩, ⟨11, 3, 3, 5⟩] = false := by decide
example : checkInterval 10 12 [⟨11, 3, 3, 5⟩] = false := by decide
example : checkInterval 9 8 [] = true := by decide
example : checkInterval 1 5 [] = false := by decide
example : checkInterval 7 1000 regressionCertificates = false := by decide

example (n : ℕ) (hlo : 9 ≤ n) (hhi : n ≤ 1000) (hodd : Odd n) :
    LiuWang.IsThreeOddPrimeSum n :=
  threeOddPrimes_9_1000 n hlo hhi hodd

example : LiuWang.IsThreeOddPrimeSum 9 :=
  threeOddPrimes_on_certified_union (by decide) (by decide) (Or.inl (by decide))
    (by intro h; omega)

example : LiuWang.IsThreeOddPrimeSum 999 :=
  threeOddPrimes_9_1000 999 (by decide) (by decide) (by
    exact ⟨499, rfl⟩)

end LiuWang.Proof.FiniteTernaryClosure
