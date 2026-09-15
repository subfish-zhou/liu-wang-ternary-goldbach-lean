import LiuWang.Proof.ArithmeticBounds.ContinuationConsumer

set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs false

open LiuWang.Proof.ArithmeticBounds
open LiuWang.Proof.ArithmeticBounds.ContinuationHelpers

#print sievePrimes
#print dvdIndicator
#print oddSquareIndicator
#print sieveForm
#print oddDensity
#print sourceLargeDivisorWeight
#print sourceVaughanInnerSupport
#print sourceVaughanInnerSum
#check @sievePrimes_card
#print axioms sievePrimes_card
#check @sievePrimes_prime
#print axioms sievePrimes_prime
#check @dvdIndicator_mul
#print axioms dvdIndicator_mul
#check @oddSquareIndicator_eq
#print axioms oddSquareIndicator_eq
#check @sieveForm_indicator_eq
#print axioms sieveForm_indicator_eq
#check @sieveForm_indicator_nonneg
#print axioms sieveForm_indicator_nonneg
#check @abs_moebius_le_sieveForm
#print axioms abs_moebius_le_sieveForm
#check @sum_sieveForm
#print axioms sum_sieveForm
#check @sieveForm_le
#print axioms sieveForm_le
#check @sieve_density_le
#print axioms sieve_density_le
#check @sum_dvdIndicator_Ioc
#print axioms sum_dvdIndicator_Ioc
#check @dyadic_dvdIndicator_bounds
#print axioms dyadic_dvdIndicator_bounds
#check @dyadic_oddSquareIndicator_bounds
#print axioms dyadic_oddSquareIndicator_bounds
#check @sum_abs_moebius_dyadic_le_linear
#print axioms sum_abs_moebius_dyadic_le_linear
#check @sum_abs_moebius_dyadic_le_6111
#print axioms sum_abs_moebius_dyadic_le_6111
#check @fourHundredThousand_le_exp_13066
#print axioms fourHundredThousand_le_exp_13066
#check @sum_abs_moebius_dyadic_source_620
#print axioms sum_abs_moebius_dyadic_source_620
#check @mem_moebius_dyadic_iff
#print axioms mem_moebius_dyadic_iff
#check @sourceVaughanV_ge_exp_13066
#print axioms sourceVaughanV_ge_exp_13066
#check @sum_abs_moebius_sourceVaughan_block
#print axioms sum_abs_moebius_sourceVaughan_block
#check @abs_moebius_sq
#print axioms abs_moebius_sq
#check @moebius_weighted_cauchy
#print axioms moebius_weighted_cauchy
#check @moebius_dyadic_cauchy_6111
#print axioms moebius_dyadic_cauchy_6111
#check @sourceVaughan_block_cauchy
#print axioms sourceVaughan_block_cauchy
#check @mem_sourceVaughanInnerSupport_iff
#print axioms mem_sourceVaughanInnerSupport_iff
#check @sourceVaughan_actual_inner_cauchy
#print axioms sourceVaughan_actual_inner_cauchy
