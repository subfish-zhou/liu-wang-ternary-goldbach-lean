import LiuWang

/-! Executable usage examples. These reuse existing producers; they are not new analytic estimates. -/
open scoped BigOperators Interval
open AnalyticNumberTheory.LargeSieve

example (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖∑ n ∈ s, a n * charReal ((n : ℝ) * x)‖ ^ 2) =
      ∑ n ∈ s, ‖a n‖ ^ 2 := by
  simpa using chen1973_fourier_parseval s a 0

example (n u v : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      AnalyticNumberTheory.Sieve.vaughanFirst n u +
      AnalyticNumberTheory.Sieve.vaughanSecond n u v +
      AnalyticNumberTheory.Sieve.vaughanThird n u v :=
  AnalyticNumberTheory.Sieve.vaughanIdentity n u v

example : RawLandauSiegelLowerBound :=
  fourFactor_rawLandauSiegelLowerBound

example : NonprincipalPrimitivePsiSiegelWalfiszSource :=
  fourFactor_nonprincipalPrimitivePsiSiegelWalfiszSource

example : MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  fourFactor_standardBombieriVinogradov
