import LiuWang.Proof.NonSymmetricContour.Consumer
import LiuWang.Proof.NonSymmetricContour.Origin

/-! # 所有新增公开声明的完整类型与标准公理审计 -/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option format.width 120

open LiuWang.Proof.NonSymmetricContour

#check @centeredKernel
#print axioms centeredKernel
#check @centeredKernel_eq
#print axioms centeredKernel_eq
#check @differentiable_centeredKernel
#print axioms differentiable_centeredKernel
#check @centeredKernel_zero
#print axioms centeredKernel_zero
#check @analyticIntegrand
#print axioms analyticIntegrand
#check @analyticIntegrand_eq
#print axioms analyticIntegrand_eq
#check @meromorphic_analyticIntegrand
#print axioms meromorphic_analyticIntegrand
#check @analyticAt_analyticIntegrand
#print axioms analyticAt_analyticIntegrand
#check @simple_analyticIntegrand
#print axioms simple_analyticIntegrand
#check @residue_analyticIntegrand
#print axioms residue_analyticIntegrand
#check @residue_analyticIntegrand_zero
#print axioms residue_analyticIntegrand_zero
#check @residue_horizontalIntegrand_zero
#print axioms residue_horizontalIntegrand_zero
#check @rectangleZeroIndices
#print axioms rectangleZeroIndices
#check @mem_rectangleZeroIndices
#print axioms mem_rectangleZeroIndices
#check @rectangleZeroValues
#print axioms rectangleZeroValues
#check @zero_not_mem_rectangleZeroValues
#print axioms zero_not_mem_rectangleZeroValues
#check @rectangleZeroFiber_card
#print axioms rectangleZeroFiber_card
#check @sum_rectangleZeroValues_multiplicity
#print axioms sum_rectangleZeroValues_multiplicity
#check @lowerLeft
#print axioms lowerLeft
#check @upperRight
#print axioms upperRight
#check @lowerLeft_re
#print axioms lowerLeft_re
#check @lowerLeft_im
#print axioms lowerLeft_im
#check @upperRight_re
#print axioms upperRight_re
#check @upperRight_im
#print axioms upperRight_im
#check @mem_rectangle
#print axioms mem_rectangle
#check @mem_border
#print axioms mem_border
#check @zero_not_mem_border
#print axioms zero_not_mem_border
#check @LFunction_ne_zero_border
#print axioms LFunction_ne_zero_border
#check @verticalIntegral
#print axioms verticalIntegral
#check @horizontalIntegral
#print axioms horizontalIntegral
#check @threeSides
#print axioms threeSides
#check @rectangle_orientation
#print axioms rectangle_orientation
#check @norm_verticalIntegral
#print axioms norm_verticalIntegral
#check @norm_horizontalIntegral
#print axioms norm_horizontalIntegral
#check @AdmissibleHeights
#print axioms AdmissibleHeights
#check @sourceT_large
#print axioms sourceT_large
#check @exists_admissibleHeights
#print axioms exists_admissibleHeights
#check @admissibleHeights_signs
#print axioms admissibleHeights_signs
#check @admissibleHeights_line
#print axioms admissibleHeights_line
#check @admissibleHeights_border
#print axioms admissibleHeights_border
#check @admissibleHeights_horizontal_budget
#print axioms admissibleHeights_horizontal_budget
#check @rectangle_residue_identity
#print axioms rectangle_residue_identity
#check @right_integral_add_zeros_add_origin_eq_threeSides
#print axioms right_integral_add_zeros_add_origin_eq_threeSides
#check @log_le_div_250
#print axioms log_le_div_250
#check @source_log_qT_bounds
#print axioms source_log_qT_bounds
#check @horizontal_cost_le_budget
#print axioms horizontal_cost_le_budget
#check @norm_origin_le_budget
#print axioms norm_origin_le_budget
#check @threeSides_and_origin_cost_le_budget
#print axioms threeSides_and_origin_cost_le_budget
#check @centeredZeroSum
#print axioms centeredZeroSum
#check @actual_source_rectangle_estimate
#print axioms actual_source_rectangle_estimate
#check @Consumer.actual_centered_identity_all_real_endpoints
#print axioms Consumer.actual_centered_identity_all_real_endpoints
