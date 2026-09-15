import LiuWang.Proof.PrimePowerRemoval.Main

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

open LiuWang.Proof.PrimePowerRemoval

#check @primePowerWeight_eq_nonprime
#print axioms primePowerWeight_eq_nonprime
#check @primePowerWeight_nonneg
#print axioms primePowerWeight_nonneg
#check @primePowerWeight_pos_iff
#print axioms primePowerWeight_pos_iff
#check @primePowerWeight_pos_iff_exists_prime_pow
#print axioms primePowerWeight_pos_iff_exists_prime_pow
#check @primePowerMass_le_psi_sub_theta
#print axioms primePowerMass_le_psi_sub_theta
#check @primePowerMass_le_sqrt_mul_log
#print axioms primePowerMass_le_sqrt_mul_log
#check @I_nonneg
#print axioms I_nonneg
#check @I_le_lambdaTripleCount
#print axioms I_le_lambdaTripleCount
#check @lambdaTripleCount_sub_I_eq_nonprime_triples
#print axioms lambdaTripleCount_sub_I_eq_nonprime_triples
#check @lambdaTripleCount_sub_I_le
#print axioms lambdaTripleCount_sub_I_le
#check @primePowerRemoval
#print axioms primePowerRemoval
#check @exists_window_primes_of_I_pos
#print axioms exists_window_primes_of_I_pos
#check @isThreeOddPrimeSum_of_I_pos
#print axioms isThreeOddPrimeSum_of_I_pos
#check @lambdaTripleCount_sub_I_lt_budget
#print axioms lambdaTripleCount_sub_I_lt_budget
#check @I_lower_bound_of_lambda_lower_bound
#print axioms I_lower_bound_of_lambda_lower_bound
#check @isThreeOddPrimeSum_of_lambda_lower_bound
#print axioms isThreeOddPrimeSum_of_lambda_lower_bound
