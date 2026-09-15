import LiuWang.Proof.SmallConductorExclusion.Consumer

/-!
# Small-conductor exclusion: a nonempty certified coverage family

`PeriodPrefixNonnegative` is a finite test on actual character values. It implies
strict positivity of the real part of the original `LFunction` at every real
`sigma > 0`, with the quantitative lower bound `1 - 2^(-sigma)`.

All nonprincipal characters modulo three and four satisfy the test. The
explicit primitive quadratic character `datumFour` proves nonemptiness.
The frozen R24 family theorem consumes this producer without changing its
ordinary L-function, pole guard, closed height, common source or multiplicities;
the actual exceptional primitive conductor is consequently at least five.

The original paper uses `9.645908801` rather than `24`. The real-axis producer
is independent of either region constant: `certified_source_original_region_ne_zero`
also explicitly pays the original closed real interval. The full complex-region
consumer here is only the already proved R24 theorem. No coverage of every conductor below 987,
no widening of the general zero region, and no Goldbach conclusion is claimed.
-/
