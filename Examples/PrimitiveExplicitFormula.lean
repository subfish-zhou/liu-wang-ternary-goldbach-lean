import LiuWang
set_option autoImplicit false
namespace BombieriVinogradov.SiegelWalfisz
example :
    exists c : Real, And (0 < c)
      (And (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        3 <= N -> Ne chi 1 -> ExplicitFormulaZeroFreeData c chi)
      (exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N], 3 <= N ->
          forall {chi : DirichletCharacter Complex N},
            Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 <= x ->
              forall {T : Real}, 2 <= T -> T <= x ->
                forall (exceptional : Option Complex),
                  IsExceptionalZeroChoice c chi exceptional ->
                    norm (characterChebyshevSum x chi +
                      truncatedCriticalZeroSum chi x T exceptional +
                      exceptionalZeroContribution x exceptional) <=
                    C * explicitFormulaRemainderMajorant N x T))) := by
  exact BombieriVinogradov.SiegelWalfisz.exists_primitiveExplicitFormula_at_least_two
end BombieriVinogradov.SiegelWalfisz
