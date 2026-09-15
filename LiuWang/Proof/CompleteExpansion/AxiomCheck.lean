import LiuWang.Proof.CompleteExpansion.Consumer
import LiuWang.Proof.PrincipalExpansion.AxiomCheck

/-! # 实际全 S 强零点展开：公开定义、类型和标准公理 -/

set_option format.width 120
set_option pp.universes true

open LiuWang.Proof.CompleteExpansion

#print principalCoefficient
#print principalMass
#print nonprincipalMass
#print zeroPacket
#print nonprincipalError
#print errorBound
#print zeroValues
#print zeroValueSum

#check @norm_principalCoefficient
#check @principalMass_nonneg
#check @nonprincipalMass_nonneg
#check @zeroPacket_eq_gauss
#check @complete_error_identity
#check @norm_nonprincipalError_le
#check @complete_error_of_bounds
#check @nonprincipalMass_le_totient
#check @nonprincipalMass_le_modulus
#check @nonprincipalMass_one
#check @principalCoefficient_one
#check @principalMass_one
#check @zeroPacket_one
#check @complete_modulus_one_identity
#check @complete_error_function
#check @errorBound_le_decimal
#check @complete_error_decimal
#check @complete_error_totient
#check @complete_error_modulus
#check @errorBound_one
#check @complete_modulus_one_function
#check @nonprincipal_zero_window
#check @mem_zeroValues
#check @zeroValues_pole_excluded
#check @zeroValueSum_principal
#check @zeroValueSum_nonprincipal
#check @zeroPacket_eq_all_values
#check @zeroValues_eq_literal
#check @zeroPacket_values_one
#check @complete_values_function
#check @S_eq_closed_sum
#check @window_eq_literal
#check @complete_closed_window
#check @complete_values_totient
#check @complete_modulus_one_values
#check @modulus_one_corrections

#print axioms complete_error_function
#print axioms complete_error_decimal
#print axioms complete_error_totient
#print axioms complete_error_modulus
#print axioms nonprincipal_zero_window
#print axioms mem_zeroValues
#print axioms zeroPacket_eq_all_values
#print axioms complete_values_function
#print axioms complete_closed_window
#print axioms complete_values_totient
#print axioms complete_modulus_one_values
#print axioms modulus_one_corrections
