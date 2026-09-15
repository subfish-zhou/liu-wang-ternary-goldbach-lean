import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.CellData
import Lean.PrettyPrinter.Delaborator

set_option autoImplicit false

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

open Lean Elab Command

elab "recovery_sum " name:ident " from " start:num " count " count:num
    " using " "[" proofs:ident,* "]" : command => do
  let terms := proofs.getElems
  if terms.isEmpty then throwError "A recovery sum requires existing proved bounds"
  let mut proof : TSyntax `term := ⟨terms[0]!.raw⟩
  for term in terms[1:] do
    proof ← `(add_le_add $proof $term)
  let rhs ← liftTermElabM do
    let e ← Term.elabTerm (← `(by
      have h := $proof
      norm_num [Finset.sum_range_succ] at h
      exact h)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← Meta.inferType (← instantiateMVars e)
    PrettyPrinter.delab type.getAppArgs.back!
  elabCommand (← `(theorem $name :
    (∑ i ∈ Finset.range $count, refinedCellUpper ($start + i)) ≤ $rhs := by
      have h := $proof
      norm_num [Finset.sum_range_succ] at h
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, zero_add]
      simpa only [add_assoc] using h))

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
