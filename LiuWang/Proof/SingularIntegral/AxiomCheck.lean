import LiuWang.Proof.SingularIntegral.Consumer

/-! # 全部新增声明的类型、定义值及传递公理审计 -/

open LiuWang.Proof.SingularIntegral

#print sourceSimplex
#print triangle
#print windowWeight
#print weightMass
#print weightVariation
#print tripleConvolution
#print LiuWang.Proof.Interfaces.J
#print LiuWang.Proof.Interfaces.Jrho
#print LiuWang.Proof.Interfaces.sourceWindowLower
#print AnalyticNumberTheory.LargeSieve.charReal

#check @sourceSimplex_eq_triangle
#check @mem_sourceSimplex_iff_coordinates
#check @triangle_isCompact
#check @triangle_measurableSet
#check @triangle_iterated_area
#check @triangle_iterated_area_complex
#check @triangle_two_dimensional_scaling
#check @window_lower_pos
#check @window_lower_le
#check @cpow_continuousOn_window
#check @cpow_intervalIntegrable
#check @windowWeight_integrable
#check @windowWeight_stronglyMeasurable
#check @charReal_eq_fourierChar
#check @charReal_norm
#check @charReal_continuous
#check @Jrho_intervalIntegrable
#check @Jrho_eq_fourier_neg
#check @Jrho_eq_fourierInv
#check @Jrho_one_eq_J
#check @simplex_cpow_continuousOn
#check @simplex_cpow_integrableOn
#check @weightMass_nonneg
#check @weightVariation_nonneg
#check @Jrho_norm_le_mass
#check @cpow_hasDerivAt
#check @charReal_mul_hasDerivAt
#check @Jrho_integrationByParts
#check @Jrho_abs_mul_norm_le_variation
#check @Jrho_continuous
#check @Jrho_pair_integrable
#check @Jrho_triple_integrable
#check @windowWeight_bounded
#check @windowWeight_continuousAt
#check @convolution_window_continuous
#check @convolution_window_bounded
#check @tripleConvolution_integrable
#check @tripleConvolution_continuous
#check @fourier_tripleConvolution
#check @Jrho_product_integrable
#check @fourier_tripleConvolution_integrable
#check @integral_Jrho_triple_eq_convolution
#check @integral_triangle_indicator_slice
#check @integral_triangle_eq_iterated
#check @triangle_outer_intervalIntegrable
#check @triangle_volume
#check @sourceSimplex_volume
#check @simplex_cpow_inner_intervalIntegrable
#check @simplex_cpow_outer_intervalIntegrable
#check @scaled_window_conditions
#check @window_product_eq_triangle_indicator
#check @tripleConvolution_eq_scaled_triangle
#check @integral_Jrho_triple_eq_simplex
#check @integral_J_triple
#check @lemma4_1_2000
#check @integral_Jrho_triple_eq_sourceSimplex
#check @J_cube_integrable
#check @integral_J_cube
#check @integral_J_cube_2000
#check @J_cube_integrable_2000
#check @convolution_integrand_integrable_of_bounded_right
#check @window_pair_convolutionExists
#check @window_triple_convolutionExists

#print axioms sourceSimplex
#print axioms triangle
#print axioms windowWeight
#print axioms weightMass
#print axioms weightVariation
#print axioms tripleConvolution
#print axioms sourceSimplex_eq_triangle
#print axioms mem_sourceSimplex_iff_coordinates
#print axioms triangle_isCompact
#print axioms triangle_measurableSet
#print axioms triangle_iterated_area
#print axioms triangle_iterated_area_complex
#print axioms triangle_two_dimensional_scaling
#print axioms window_lower_pos
#print axioms window_lower_le
#print axioms cpow_continuousOn_window
#print axioms cpow_intervalIntegrable
#print axioms windowWeight_integrable
#print axioms windowWeight_stronglyMeasurable
#print axioms charReal_eq_fourierChar
#print axioms charReal_norm
#print axioms charReal_continuous
#print axioms Jrho_intervalIntegrable
#print axioms Jrho_eq_fourier_neg
#print axioms Jrho_eq_fourierInv
#print axioms Jrho_one_eq_J
#print axioms simplex_cpow_continuousOn
#print axioms simplex_cpow_integrableOn
#print axioms weightMass_nonneg
#print axioms weightVariation_nonneg
#print axioms Jrho_norm_le_mass
#print axioms cpow_hasDerivAt
#print axioms charReal_mul_hasDerivAt
#print axioms Jrho_integrationByParts
#print axioms Jrho_abs_mul_norm_le_variation
#print axioms Jrho_continuous
#print axioms Jrho_pair_integrable
#print axioms Jrho_triple_integrable
#print axioms windowWeight_bounded
#print axioms windowWeight_continuousAt
#print axioms convolution_window_continuous
#print axioms convolution_window_bounded
#print axioms tripleConvolution_integrable
#print axioms tripleConvolution_continuous
#print axioms fourier_tripleConvolution
#print axioms Jrho_product_integrable
#print axioms fourier_tripleConvolution_integrable
#print axioms integral_Jrho_triple_eq_convolution
#print axioms integral_triangle_indicator_slice
#print axioms integral_triangle_eq_iterated
#print axioms triangle_outer_intervalIntegrable
#print axioms triangle_volume
#print axioms sourceSimplex_volume
#print axioms simplex_cpow_inner_intervalIntegrable
#print axioms simplex_cpow_outer_intervalIntegrable
#print axioms scaled_window_conditions
#print axioms window_product_eq_triangle_indicator
#print axioms tripleConvolution_eq_scaled_triangle
#print axioms integral_Jrho_triple_eq_simplex
#print axioms integral_J_triple
#print axioms lemma4_1_2000
#print axioms integral_Jrho_triple_eq_sourceSimplex
#print axioms J_cube_integrable
#print axioms integral_J_cube
#print axioms integral_J_cube_2000
#print axioms J_cube_integrable_2000
#print axioms convolution_integrand_integrable_of_bounded_right
#print axioms window_pair_convolutionExists
#print axioms window_triple_convolutionExists

#check @Real.fourier_mul_convolution_eq
#check @MeasureTheory.Integrable.fourierInv_fourier_eq
#check @LiuWang.Proof.Parameters.nat_pos_of_exp_le
#print axioms Real.fourier_mul_convolution_eq
#print axioms MeasureTheory.Integrable.fourierInv_fourier_eq
#print axioms LiuWang.Proof.Parameters.nat_pos_of_exp_le
