import LiuWang.Proof.NonprincipalPsi.Consumer

/-! # 完整公开类型、实际定义及标准公理闭包 -/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option format.width 120

open LiuWang.Proof.NonprincipalPsi

#check @conductor_source_domain
#print axioms conductor_source_domain
#check @norm_psi_sub_primitive_le
#print axioms norm_psi_sub_primitive_le
#check @induction_cost_source_le
#print axioms induction_cost_source_le
#check @norm_psi_sub_primitive_source_le
#print axioms norm_psi_sub_primitive_source_le
#check @psi_primitive_highZeroSum_source_le
#print axioms psi_primitive_highZeroSum_source_le
#check @completedZeroValue_re_lt_one_of_pos
#print axioms completedZeroValue_re_lt_one_of_pos
#check @mem_highZeroIndices_nonprincipal
#print axioms mem_highZeroIndices_nonprincipal
#check @highZeroValues_eq_primitive
#print axioms highZeroValues_eq_primitive
#check @highZeroFiber_card
#print axioms highZeroFiber_card
#check @sum_highZeroValues_multiplicity
#print axioms sum_highZeroValues_multiplicity
#check @sum_highZeroIndices_eq_primitive
#print axioms sum_highZeroIndices_eq_primitive
#check @highZeroSum_eq_primitive
#print axioms highZeroSum_eq_primitive
#check @psi_highZeroSum_source_le_strong
#print axioms psi_highZeroSum_source_le_strong
#check @psi_highZeroSum_source_le
#print axioms psi_highZeroSum_source_le
#check @nonprincipal_psi_sum_strong
#print axioms nonprincipal_psi_sum_strong
#check @nonprincipal_psi_sum
#print axioms nonprincipal_psi_sum
#check @nonprincipal_psi_sum_multiplicity_strong
#print axioms nonprincipal_psi_sum_multiplicity_strong

#print highZeroValues
#print LiuWang.Proof.Interfaces.sourceL
#print LiuWang.Proof.Interfaces.sourceT
#print LiuWang.Proof.Interfaces.sourceP1
#print LiuWang.Proof.Interfaces.sourceWindowLower
#print LiuWang.Proof.ExplicitPerron.psi
#print BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
#print LiuWang.Proof.FixedHeightZeroSum.highZeroSum
#print LiuWang.Proof.FixedHeightZeroSum.highZeroIndices
#print LiuWang.Proof.FixedHeightZeroSum.fixedZeroIndices
#print LiuWang.Proof.Interfaces.criticalZeroIndices
#print LiuWang.Proof.Interfaces.CompletedZeroIndex
#print LiuWang.Proof.Interfaces.completedZeroValue
#print BombieriVinogradov.SiegelWalfisz.SymmetricCompletedZeroIndex
#print BombieriVinogradov.SiegelWalfisz.symmetricCompletedLFunction
#print Complex.Hadamard.divisorZeroIndex₀
#print Complex.Hadamard.divisorZeroIndex

#check @LiuWang.Proof.PerronBudget.psi_highZeroSum_source_le_strong
#print axioms LiuWang.Proof.PerronBudget.psi_highZeroSum_source_le_strong
#check @LiuWang.Proof.PerronBudget.primitive_nonprincipal_psi_sum_strong
#print axioms LiuWang.Proof.PerronBudget.primitive_nonprincipal_psi_sum_strong
#check @BombieriVinogradov.SiegelWalfisz.norm_characterChebyshevSum_sub_primitive_le
#print axioms BombieriVinogradov.SiegelWalfisz.norm_characterChebyshevSum_sub_primitive_le
#check @BombieriVinogradov.SiegelWalfisz.completedDivisorMultiplicity_eq_primitive
#print axioms BombieriVinogradov.SiegelWalfisz.completedDivisorMultiplicity_eq_primitive
#check @BombieriVinogradov.SiegelWalfisz.analyticOrderNatAt_LFunction_eq_primitive
#print axioms BombieriVinogradov.SiegelWalfisz.analyticOrderNatAt_LFunction_eq_primitive
