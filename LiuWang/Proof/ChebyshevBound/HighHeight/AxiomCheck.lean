import LiuWang.Proof.ChebyshevBound.HighHeight.IntegratedPsi

/-! # 本轮承重前缀的类型、实际定义和递归公理入口；不声明尖锐 ψ 上界。 -/

set_option pp.universes true
set_option pp.fullNames true
set_option pp.notation false

open LiuWang.Proof.ChebyshevBound.HighHeight

#check xiTerm_sum_one
#check zeta_ne_zero_height_le_one
#check zeta_quartic_nonneg
#check zeta_zero_free_twenty
#check xiHeightTail_sum_le
#check xiZeroWeight_sum_le
#check integratedZeroTerm_norm_sum_le
#check integratedZeroSum_source_norm_le
#check integratedZeroSum_difference_le
#check integrated_zero_desmoothing_budget
#check psi_le_integrated_difference
#check sum_mangoldt_le_integrated_difference
#check archimedean_psi_correction_nonpos

#print xiTerm
#print xiHeightTail
#print xiZeroWeight
#print xiLayerMajorant
#print integratedZeroTerm
#print integratedPsi

#print axioms xiTerm_sum_one
#print axioms zeta_ne_zero_height_le_one
#print axioms zeta_quartic_nonneg
#print axioms zeta_zero_free_twenty
#print axioms xiHeightTail_sum_le
#print axioms xiZeroWeight_sum_le
#print axioms integratedZeroTerm_norm_sum_le
#print axioms integratedZeroSum_source_norm_le
#print axioms integratedZeroSum_difference_le
#print axioms integrated_zero_desmoothing_budget
#print axioms psi_le_integrated_difference
#print axioms sum_mangoldt_le_integrated_difference
#print axioms archimedean_psi_correction_nonpos
