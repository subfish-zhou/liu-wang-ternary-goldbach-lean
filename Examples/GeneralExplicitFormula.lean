import LiuWang

open BombieriVinogradov.SiegelWalfisz
set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true

example :
    exists c : Real, And (0 < c)
      (And (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
        Ne chi 1 -> ExplicitFormulaZeroFreeData c chi)
      (exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N] {chi : _root_.DirichletCharacter Complex N},
          Ne chi 1 -> forall {x : Nat}, 2 <= x ->
            forall {T : Real}, 2 <= T -> T <= x ->
              forall (e : Option Complex), IsExceptionalZeroChoice c chi e ->
                norm (characterChebyshevSum x chi + truncatedCriticalZeroSum chi x T e +
                  exceptionalZeroContribution x e) <=
                    C * explicitFormulaRemainderMajorant N x T))) := dirichletExplicitFormula

#check @dirichletExplicitFormula
#print axioms dirichletExplicitFormula
#print characterChebyshevSum
#print IsExceptionalZeroChoice
#print truncatedCriticalZeroSum
#print explicitFormulaRemainderMajorant
