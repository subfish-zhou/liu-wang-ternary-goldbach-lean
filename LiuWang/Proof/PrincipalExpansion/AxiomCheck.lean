import LiuWang.Proof.PrincipalExpansion.Consumer

/-! # 强主字符闭窗振荡的公开定义、类型与标准公理 -/

set_option format.width 120
set_option pp.universes true

open LiuWang.Proof.PrincipalExpansion

#print zeroSum
#print abelError
#print errorFunction

#check @zeroSum_eq_values
#check @J_eq_abelTransform
#check @identity_phase_integrable
#check @abelTransform_sub
#check @principal_highZeroSum_phase_integrable
#check @zeroSum_eq_abelTransform
#check @principal_error_identity
#check @principal_error_of_slope
#check @principal_error_function
#check @modulus_one_error_function
#check @errorFunction_nonneg
#check @errorFunction_le_decimal
#check @principal_error_decimal
#check @principal_twisted_values
#check @principal_closed_window
#check @principal_zero_window

#print axioms principal_error_identity
#print axioms principal_error_of_slope
#print axioms principal_error_function
#print axioms modulus_one_error_function
#print axioms principal_closed_window
