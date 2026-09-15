import LiuWang

open Finset MeasureTheory AnalyticNumberTheory.LargeSieve LiuWang.Fourier
open scoped BigOperators Interval

#check @LiuWang.Fourier.indexedExpSum
#check @LiuWang.Fourier.integral_indexedExpSum_triple
#check @LiuWang.Fourier.integral_finiteExpSum_triple
#check @LiuWang.Fourier.liuWangSupport
#check @LiuWang.Fourier.mem_liuWangSupport
#check @LiuWang.Fourier.liuWangExpSum
#check @LiuWang.Fourier.liuWangTernarySum
#check @LiuWang.Fourier.integral_liuWangExpSum_cube

#print axioms LiuWang.Fourier.indexedExpSum
#print axioms LiuWang.Fourier.integral_indexedExpSum_triple
#print axioms LiuWang.Fourier.integral_finiteExpSum_triple
#print axioms LiuWang.Fourier.liuWangSupport
#print axioms LiuWang.Fourier.mem_liuWangSupport
#print axioms LiuWang.Fourier.liuWangExpSum
#print axioms LiuWang.Fourier.liuWangTernarySum
#print axioms LiuWang.Fourier.integral_liuWangExpSum_cube
#print axioms AnalyticNumberTheory.LargeSieve.charReal_intervalIntegral_int

#print LiuWang.Fourier.liuWangSupport
#print LiuWang.Fourier.liuWangExpSum
#print LiuWang.Fourier.liuWangTernarySum

-- A real imported consumer: the requested Λ-weighted identity on [0,1].
example (N : ℕ) :
    (∫ α in (0 : ℝ)..1, liuWangExpSum N α ^ 3 * charReal (-(N : ℝ) * α)) =
      (liuWangTernarySum N : ℂ) := by
  simpa using integral_liuWangExpSum_cube N 0

-- Independent spectra, arbitrary complex weights, possibly negative target.
example (s t v : Finset ℤ) (a b c : ℤ → ℂ) (N : ℤ) :
    (∫ α in (0 : ℝ)..1,
      (∑ i ∈ s, a i * charReal ((i : ℝ) * α)) *
      (∑ j ∈ t, b j * charReal ((j : ℝ) * α)) *
      (∑ k ∈ v, c k * charReal ((k : ℝ) * α)) *
        charReal (-(N : ℝ) * α)) =
      ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ v,
        if i + j + k = N then a i * b j * c k else 0 := by
  simpa using integral_finiteExpSum_triple s t v a b c N 0
