import LiuWang.Proof.EffectiveLValue.EvenConsumer
import LiuWang.Proof.EffectiveLValue.OddAxiomCheck

/-!
The odd audit import makes the shared-core regression part of the same kernel
check. No even mathematical proof imports the odd Abel wrapper.
-/

open LiuWang.Proof.EffectiveLValue

set_option pp.all true

#check @primitiveCharacter_ne_one
#check @realCharacter_zero
#check @realCharacter_gauss_fourier
#check @realCharacter_tendsto_abel
#check @realCharacter_abel_log
#check @stdAddChar_sub_one_mem_slitPlane
#check @realCharacter_gauss_mul_LFunction_one_log
#check @realCharacterSign
#check @realCharacterSign_cast
#check @realCharacterSign_zero
#check @realCharacterSign_sum
#check @characterCyclotomicProduct
#check @stdAddChar_one_sub_ne_zero
#check @characterCyclotomicProduct_eq_exp
#check @characterCyclotomicProduct_eq_exp_LFunction
#check @stdAddChar_isIntegral
#check @stdAddChar_pow_val_mul
#check @stdAddChar_ratio_eq_geom_sum
#check @stdAddChar_ratio_isIntegral
#check @characterCyclotomicProduct_eq_normalized
#check @characterCyclotomicProduct_isIntegral
#check @characterCyclotomicProduct_inv_isIntegral
#check @even_characterGaussSum_im
#check @even_characterGaussSum_abs_re
#check @even_characterGaussSum_re_sq
#check @evenCharacter_LFunction_one_signed
#check @evenCharacter_LFunction_one_formula
#check @evenCharacter_product_eq_real_exp
#check @evenCharacter_product_pos
#check @evenCharacter_product_im
#check @evenCharacter_abs_log_product
#check @evenCharacter_product_ne_one
#check @characterCyclotomicAmbient
#check @stdAddChar_one_isPrimitiveRoot
#check @characterCyclotomicAmbient_cyclotomic
#check @characterCyclotomicAmbient_finite
#check @characterCyclotomicAmbient_galois
#check @characterCyclotomicRoot
#check @characterCyclotomicRoot_pow
#check @characterCyclotomicRoot_primitive
#check @characterCyclotomicAutIndex
#check @characterCyclotomicRoot_aut
#check @characterCyclotomicProductInField
#check @characterCyclotomicProductInField_coe
#check @realCharacterSign_mul
#check @realCharacterSign_unit
#check @characterCyclotomicProductInField_aut
#check @characterCyclotomicProductInField_aut_cases
#check @characterGaussSumInField
#check @characterGaussSumInField_coe
#check @characterGaussSumInField_aut
#check @characterCyclotomicProduct_trace_int
#check @characterCyclotomicProduct_gauss_quotient_rat
#check @evenCharacter_product_coe_re
#check @evenCharacter_product_pell_rat
#check @evenCharacterLargeProduct
#check @evenCharacterLargeProduct_gt_one
#check @evenCharacterLargeProduct_log
#check @evenCharacterLargeProduct_pell_rat
#check @EvenConsumer.actual_even_logarithm
#check @EvenConsumer.actual_even_integral_product
#check @EvenConsumer.actual_even_pell_prefix
#check @EvenConsumer.cutoff_987_pell_prefix

set_option pp.all false

#print axioms primitiveCharacter_ne_one
#print axioms realCharacter_zero
#print axioms realCharacter_gauss_fourier
#print axioms realCharacter_tendsto_abel
#print axioms realCharacter_abel_log
#print axioms stdAddChar_sub_one_mem_slitPlane
#print axioms realCharacter_gauss_mul_LFunction_one_log
#print axioms realCharacterSign
#print axioms realCharacterSign_cast
#print axioms realCharacterSign_zero
#print axioms realCharacterSign_sum
#print axioms characterCyclotomicProduct
#print axioms stdAddChar_one_sub_ne_zero
#print axioms characterCyclotomicProduct_eq_exp
#print axioms characterCyclotomicProduct_eq_exp_LFunction
#print axioms stdAddChar_isIntegral
#print axioms stdAddChar_pow_val_mul
#print axioms stdAddChar_ratio_eq_geom_sum
#print axioms stdAddChar_ratio_isIntegral
#print axioms characterCyclotomicProduct_eq_normalized
#print axioms characterCyclotomicProduct_isIntegral
#print axioms characterCyclotomicProduct_inv_isIntegral
#print axioms even_characterGaussSum_im
#print axioms even_characterGaussSum_abs_re
#print axioms even_characterGaussSum_re_sq
#print axioms evenCharacter_LFunction_one_signed
#print axioms evenCharacter_LFunction_one_formula
#print axioms evenCharacter_product_eq_real_exp
#print axioms evenCharacter_product_pos
#print axioms evenCharacter_product_im
#print axioms evenCharacter_abs_log_product
#print axioms evenCharacter_product_ne_one
#print axioms characterCyclotomicAmbient
#print axioms stdAddChar_one_isPrimitiveRoot
#print axioms characterCyclotomicAmbient_cyclotomic
#print axioms characterCyclotomicAmbient_finite
#print axioms characterCyclotomicAmbient_galois
#print axioms characterCyclotomicRoot
#print axioms characterCyclotomicRoot_pow
#print axioms characterCyclotomicRoot_primitive
#print axioms characterCyclotomicAutIndex
#print axioms characterCyclotomicRoot_aut
#print axioms characterCyclotomicProductInField
#print axioms characterCyclotomicProductInField_coe
#print axioms realCharacterSign_mul
#print axioms realCharacterSign_unit
#print axioms characterCyclotomicProductInField_aut
#print axioms characterCyclotomicProductInField_aut_cases
#print axioms characterGaussSumInField
#print axioms characterGaussSumInField_coe
#print axioms characterGaussSumInField_aut
#print axioms characterCyclotomicProduct_trace_int
#print axioms characterCyclotomicProduct_gauss_quotient_rat
#print axioms evenCharacter_product_coe_re
#print axioms evenCharacter_product_pell_rat
#print axioms evenCharacterLargeProduct
#print axioms evenCharacterLargeProduct_gt_one
#print axioms evenCharacterLargeProduct_log
#print axioms evenCharacterLargeProduct_pell_rat
#print axioms EvenConsumer.actual_even_logarithm
#print axioms EvenConsumer.actual_even_integral_product
#print axioms EvenConsumer.actual_even_pell_prefix
#print axioms EvenConsumer.cutoff_987_pell_prefix
