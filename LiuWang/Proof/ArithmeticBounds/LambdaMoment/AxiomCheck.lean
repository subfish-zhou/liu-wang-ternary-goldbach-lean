import LiuWang.Proof.ArithmeticBounds.LambdaMoment.Consumer

/-! 所有新增定义、定理的完整类型及公理锥审计。 -/

set_option autoImplicit false
set_option pp.fullNames true

namespace LiuWang.Proof.ArithmeticBounds.LambdaMoment

#print sourceLargeDivisorWeight
#print Parameters.sourceVaughanU
#print Parameters.sourceVaughanV
#print momentSupport
#print actualMoment
#print largeDivisors
#print pairMultiples
#print exponentCutoff
#print primeBases
#print powerIndices
#print exponentsFor
#print W1
#print W2
#print W3

#print axioms momentSupport
#print axioms actualMoment
#print axioms largeDivisors
#print axioms pairMultiples
#print axioms exponentCutoff
#print axioms primeBases
#print axioms powerIndices
#print axioms exponentsFor
#print axioms W1
#print axioms W2
#print axioms W3

#check @mem_momentSupport
#print axioms mem_momentSupport
#check @source_quotient_geometry
#print axioms source_quotient_geometry
#check @source_weight_eq_sum_largeDivisors
#print axioms source_weight_eq_sum_largeDivisors
#check @actualMoment_eq_ordered_divisor_pairs
#print axioms actualMoment_eq_ordered_divisor_pairs
#check @large_divisors_not_coprime
#print axioms large_divisors_not_coprime
#check @nonzero_pair_same_prime
#print axioms nonzero_pair_same_prime
#check @exponent_le_cutoff
#print axioms exponent_le_cutoff
#check @exponentsFor_card_le
#print axioms exponentsFor_card_le
#check @prime_rpow_sum_le_three
#print axioms prime_rpow_sum_le_three
#check @high_power_term_le
#print axioms high_power_term_le
#check @W2_le_cutoff
#print axioms W2_le_cutoff
#check @W3_le_cutoff
#print axioms W3_le_cutoff
#check @log_U_ge_third_L
#print axioms log_U_ge_third_L
#check @pow_eight_le_exp_twelfth
#print axioms pow_eight_le_exp_twelfth
#check @cutoff_tail_le_681
#print axioms cutoff_tail_le_681
#check @W2_le_681
#print axioms W2_le_681
#check @W2_le_25876
#print axioms W2_le_25876
#check @W3_le_681
#print axioms W3_le_681
#check @mem_powerIndices_iff
#print axioms mem_powerIndices_iff
#check @powerIndices_injective
#print axioms powerIndices_injective
#check @sum_largeDivisors_eq_powerIndices
#print axioms sum_largeDivisors_eq_powerIndices
#check @sum_powerIndices
#print axioms sum_powerIndices
#check @actualMoment_eq_prime_power_pairs
#print axioms actualMoment_eq_prime_power_pairs
#check @pairMultiples_distinct_primes
#print axioms pairMultiples_distinct_primes
#check @actualMoment_eq_same_prime_pairs
#print axioms actualMoment_eq_same_prime_pairs
#check @pairMultiples_card_le
#print axioms pairMultiples_card_le
#check @actualMoment_le_ordered_power_sum
#print axioms actualMoment_le_ordered_power_sum
#check @W1_eq_actual_prime_sum
#print axioms W1_eq_actual_prime_sum
#check @mem_exponentsFor_iff
#print axioms mem_exponentsFor_iff
#check @mem_W2_exponents_iff
#print axioms mem_W2_exponents_iff
#check @mem_W3_exponents_iff
#print axioms mem_W3_exponents_iff
#check @ordered_max_sum
#print axioms ordered_max_sum
#check @exponentCutoff_pos
#print axioms exponentCutoff_pos
#check @diagonal_sum_split
#print axioms diagonal_sum_split
#check @ordered_power_sum_eq_W1_W2_W3
#print axioms ordered_power_sum_eq_W1_W2_W3
#check @actualMoment_le_613
#print axioms actualMoment_le_613
#check @actualMoment_source_le_613
#print axioms actualMoment_source_le_613
#check @actualMoment_source_high_powers_paid
#print axioms actualMoment_source_high_powers_paid
#check @source_actual_moment
#print axioms source_actual_moment
#check @source_inner_support_subset
#print axioms source_inner_support_subset
#check @source_inner_weight_moment
#print axioms source_inner_weight_moment
#check @source_dyadic_actual_moment
#print axioms source_dyadic_actual_moment

end LiuWang.Proof.ArithmeticBounds.LambdaMoment
