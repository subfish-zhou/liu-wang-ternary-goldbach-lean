import LiuWang

open scoped Real
open Complex Filter Topology

-- The complete upstream type is consumed without any added premise.
example {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s =
      -logDeriv riemannZeta (1 - s) + log (2 * π) - digamma s + π / 2 * tan (π * s / 2) :=
  logDeriv_riemannZeta_one_sub hs hz

#check @logDeriv_riemannZeta_one_sub
#print axioms logDeriv_riemannZeta_one_sub
