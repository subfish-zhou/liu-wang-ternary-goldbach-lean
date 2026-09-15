import LiuWang.Proof.FixedHeightZeroSum.Consumer

/-! # 全部公开类型、定义值与声明公理审计 -/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option format.width 120

open LiuWang.Proof.FixedHeightZeroSum

#check @fixedZeroIndices
#print fixedZeroIndices
#print axioms fixedZeroIndices
#check @mem_fixedZeroIndices
#print axioms mem_fixedZeroIndices
#check @highZeroIndices
#print highZeroIndices
#print axioms highZeroIndices
#check @lowZeroIndices
#print lowZeroIndices
#print axioms lowZeroIndices
#check @mem_highZeroIndices
#print axioms mem_highZeroIndices
#check @mem_lowZeroIndices
#print axioms mem_lowZeroIndices
#check @lowZeroIndices_eq
#print axioms lowZeroIndices_eq
#check @sum_fixed_eq_low_add_high
#print axioms sum_fixed_eq_low_add_high
#check @fixedZeroValues
#print fixedZeroValues
#print axioms fixedZeroValues
#check @fixedZeroFiber_card
#print axioms fixedZeroFiber_card
#check @sum_fixedZeroValues_multiplicity
#print axioms sum_fixedZeroValues_multiplicity
#check @changedZeroIndices
#print changedZeroIndices
#print axioms changedZeroIndices
#check @changedZeroIndices_mem_edge
#print axioms changedZeroIndices_mem_edge
#check @ncard_edge_window_le
#print axioms ncard_edge_window_le
#check @card_changedZeroIndices_le
#print axioms card_changedZeroIndices_le
#check @norm_sum_sub_sum_le_changed
#print axioms norm_sum_sub_sum_le_changed
#check @edge_norm_ge
#print axioms edge_norm_ge
#check @norm_real_cpow_le
#print axioms norm_real_cpow_le
#check @norm_centered_kernel_edge_le
#print axioms norm_centered_kernel_edge_le
#check @norm_transport_centered_raw
#print axioms norm_transport_centered_raw
#check @norm_transport_uncentered_raw
#print axioms norm_transport_uncentered_raw
#check @transport_cost_le_budget
#print axioms transport_cost_le_budget
#check @source_sqrt_endpoint_ge_hundred_million_power
#print axioms source_sqrt_endpoint_ge_hundred_million_power
#check @low_and_center_cost_le_budget
#print axioms low_and_center_cost_le_budget
#check @fixedCenteredZeroSum
#print fixedCenteredZeroSum
#print axioms fixedCenteredZeroSum
#check @highZeroSum
#print highZeroSum
#print axioms highZeroSum
#check @card_fixedZeroIndices_le
#print axioms card_fixedZeroIndices_le
#check @norm_high_center_kernel_le
#print axioms norm_high_center_kernel_le
#check @norm_high_center_sum_le
#print axioms norm_high_center_sum_le
#check @fixedCentered_sub_high_eq
#print axioms fixedCentered_sub_high_eq
#check @norm_fixedCentered_sub_high_raw
#print axioms norm_fixedCentered_sub_high_raw
#check @norm_fixedCentered_sub_high_source_le
#print axioms norm_fixedCentered_sub_high_source_le
#check @actualRightVerticalIntegral
#print actualRightVerticalIntegral
#print axioms actualRightVerticalIntegral
#check @norm_transport_centered_source_le
#print axioms norm_transport_centered_source_le
#check @norm_transport_uncentered_source_le
#print axioms norm_transport_uncentered_source_le
#check @actual_source_high_zero_estimate
#print axioms actual_source_high_zero_estimate
#check @exists_actual_high_zero_estimate_all_real_endpoints
#print axioms exists_actual_high_zero_estimate_all_real_endpoints
#check @Consumer.actual_fixed_height_high_zeros_all_real_endpoints
#print axioms Consumer.actual_fixed_height_high_zeros_all_real_endpoints
