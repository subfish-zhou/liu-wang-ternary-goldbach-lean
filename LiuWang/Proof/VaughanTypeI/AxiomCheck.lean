import LiuWang.Proof.VaughanTypeI.Consumer

/-! # 导出项的完整类型与逻辑公理审计。 -/

open LiuWang.Proof.VaughanTypeI

#print sourceLambda1
#print sourceLambda2
#print sourceLambda3
#print sourceLambda4
#print windowSum
#print sourceS1
#print sourceS2
#print sourceS3
#print sourceS4
#check @vaughanIdentity_fourTerm
#print axioms vaughanIdentity_fourTerm
#check @sourceLambda1_eq_floor
#print axioms sourceLambda1_eq_floor
#check @sourceLambda2_eq_first
#print axioms sourceLambda2_eq_first
#check @sourceLambda3_eq_neg_middle
#print axioms sourceLambda3_eq_neg_middle
#check @sourceLambda4_eq_third
#print axioms sourceLambda4_eq_third
#check @sourceLambda_decomposition
#print axioms sourceLambda_decomposition
#check @sourceS_decomposition
#print axioms sourceS_decomposition
#check @sourceVaughanU_lt_windowLower
#print axioms sourceVaughanU_lt_windowLower
#check @sourceLambda1_eq_zero_on_window
#print axioms sourceLambda1_eq_zero_on_window
#check @sourceS1_eq_zero
#print axioms sourceS1_eq_zero
#check @sourceS_eq_actual_remainder
#print axioms sourceS_eq_actual_remainder
#print truncatedKernel
#print closedRow
#print sourceSmallDivisorCoeff
#check @truncatedKernel_nonneg
#print axioms truncatedKernel_nonneg
#check @truncatedKernel_mono
#print axioms truncatedKernel_mono
#check @truncatedKernel_int
#print axioms truncatedKernel_int
#check @norm_charReal_eq_one
#print axioms norm_charReal_eq_one
#check @sum_charReal_Icc_eq
#print axioms sum_charReal_Icc_eq
#check @norm_sum_charReal_Icc_le
#print axioms norm_sum_charReal_Icc_le
#check @sum_weighted_Icc_reverse
#print axioms sum_weighted_Icc_reverse
#check @norm_sum_weighted_Icc_le
#print axioms norm_sum_weighted_Icc_le
#check @norm_sum_log_charReal_Icc_le
#print axioms norm_sum_log_charReal_Icc_le
#check @mem_closedRow
#print axioms mem_closedRow
#check @sum_window_divisors_reindex
#print axioms sum_window_divisors_reindex
#check @norm_closedRow_charReal_le
#print axioms norm_closedRow_charReal_le
#check @norm_closedRow_log_charReal_le
#print axioms norm_closedRow_log_charReal_le
#check @sourceS2_eq_closedRows
#print axioms sourceS2_eq_closedRows
#check @norm_sourceS2_le_kernel
#print axioms norm_sourceS2_le_kernel
#check @sourceLambda3_eq_neg_divisor_sum
#print axioms sourceLambda3_eq_neg_divisor_sum
#check @abs_sourceSmallDivisorCoeff_le_log
#print axioms abs_sourceSmallDivisorCoeff_le_log
#check @sourceSmallDivisorCoeff_eq_zero
#print axioms sourceSmallDivisorCoeff_eq_zero
#check @sourceS3_eq_closedRows
#print axioms sourceS3_eq_closedRows
#check @norm_sourceS3_le_kernel
#print axioms norm_sourceS3_le_kernel
#check @norm_sourceS_sub_actualS4_le_kernel
#print axioms norm_sourceS_sub_actualS4_le_kernel
#check @distToInt_eq_abs_round
#print axioms distToInt_eq_abs_round
#check @rational_block_ball_card_le
#print axioms rational_block_ball_card_le
#check @truncatedKernel_le_length
#print axioms truncatedKernel_le_length
#check @rational_block_kernel_le
#print axioms rational_block_kernel_le
#check @rational_dist_lower
#print axioms rational_dist_lower
#check @small_index_dist_lower
#print axioms small_index_dist_lower
#check @variable_kernel_le
#print axioms variable_kernel_le
#check @source_q_million
#print axioms source_q_million
#check @one_add_log_q_le_L
#print axioms one_add_log_q_le_L
#check @sourceVaughan_log_bounds
#print axioms sourceVaughan_log_bounds
#check @kernel_N_term_le
#print axioms kernel_N_term_le
#check @kernel_q_term_le
#print axioms kernel_q_term_le
#check @sourceVaughanUV_mul_L_sq
#print axioms sourceVaughanUV_mul_L_sq
#check @sourceVaughanV_mul_L_sq_le
#print axioms sourceVaughanV_mul_L_sq_le
#check @weighted_kernel_le
#print axioms weighted_kernel_le
#check @sourceS2_bound
#print axioms sourceS2_bound
#check @sourceS3_bound
#print axioms sourceS3_bound
#check @norm_sourceS_sub_actualS4_le
#print axioms norm_sourceS_sub_actualS4_le
#check @source_typeI_large
#print axioms source_typeI_large
#check @source_typeI_large_consumer
#print axioms source_typeI_large_consumer
