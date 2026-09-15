import LiuWang
set_option autoImplicit false
namespace BombieriVinogradov.SiegelWalfisz
example :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        chi ≠ 1 ->
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            (chi ^ 2 ≠ 1 ∨ s.im ≠ 0) ->
              c / (Real.log N + Real.log (|s.im| + 2)) ≤ 1 - s.re) ∧
          (forall s t : Complex,
            0 < s.re -> 0 < t.re ->
            chi.LFunction s = 0 -> chi.LFunction t = 0 ->
            s.im = 0 -> t.im = 0 ->
            1 - s.re ≤ c / Real.log N ->
            1 - t.re ≤ c / Real.log N -> s = t) ∧
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            s.im = 0 -> 1 - s.re ≤ c / Real.log N ->
              analyticOrderNatAt chi.LFunction s = 1) := by
  exact BombieriVinogradov.SiegelWalfisz.dirichletZeroFreeRegion
end BombieriVinogradov.SiegelWalfisz
