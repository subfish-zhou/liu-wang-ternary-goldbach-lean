import LiuWang.Proof.ArithmeticBounds.PrimeMoment.Consumer

/-! 全部新增声明的类型及传递公理审计；同时展示真实系数与原参数。 -/

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

namespace LiuWang.Proof.ArithmeticBounds.PrimeMoment

#print Parameters.sourceVaughanU
#print Parameters.sourceVaughanV
#print sourceLargeDivisorWeight
#print sourceVaughanInnerSupport
#print LambdaMoment.actualMoment
#print mangoldtReciprocal
#print axioms mangoldtReciprocal

#check @log_sum_eq_mangoldt_floor
#print axioms log_sum_eq_mangoldt_floor
#check @log_sum_lower
#print axioms log_sum_lower
#check @log_sum_upper
#print axioms log_sum_upper
#check @mangoldtReciprocal_nat
#print axioms mangoldtReciprocal_nat
#check @mangoldtReciprocal_nat_bounds
#print axioms mangoldtReciprocal_nat_bounds
#check @mangoldtReciprocal_bounds
#print axioms mangoldtReciprocal_bounds
#check @continuousOn_inv_Icc
#print axioms continuousOn_inv_Icc
#check @mangoldt_log_abel
#print axioms mangoldt_log_abel
#check @integral_mangoldt_log_lower
#print axioms integral_mangoldt_log_lower
#check @mangoldt_log_interval_le
#print axioms mangoldt_log_interval_le
#check @prime_log_sq_interval_le
#print axioms prime_log_sq_interval_le
#check @W1_le_8
#print axioms W1_le_8
#check @W1_le_20
#print axioms W1_le_20
#check @log_le_hundredth
#print axioms log_le_hundredth
#check @log_source_quotient_V
#print axioms log_source_quotient_V
#check @scalar_budget_31
#print axioms scalar_budget_31
#check @source_prime_budget_31
#print axioms source_prime_budget_31
#check @actualMoment_source_le_31
#print axioms actualMoment_source_le_31
#check @source_actual_moment_31
#print axioms source_actual_moment_31
#check @source_inner_weight_moment_31
#print axioms source_inner_weight_moment_31
#check @source_dyadic_actual_moment_31
#print axioms source_dyadic_actual_moment_31

end LiuWang.Proof.ArithmeticBounds.PrimeMoment
