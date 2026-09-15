import LiuWang.Proof.MinorArcEnergy.Consumer
import LiuWang.Proof.MinorArcEnergy.Ledger

/-! 完整公开接口与递归公理检查；对象成员清单另在任务证据中保存。 -/

open LiuWang.Proof.MinorArcEnergy

#check @continuous_S
#check @continuous_energy
#check @energy_integrableOn
#check @integral_S_sq
#check @setIntegral_S_sq
#check @source_energy_eq
#check @window_subset_Icc
#check @window_sq_le_prefix
#check @source_energy_le_mother
#check @source_energy_le_sharp
#check @set_energy_nonneg
#check @set_energy_le_source
#check @circleKernel_integrableOn
#check @norm_circleKernel
#check @norm_setIntegral_le_local_energy
#check @norm_setIntegral_le_source_energy
#check @repaid_mother_nonneg
#check @M4_integral_le_repaid_local_energy
#check @M4_integral_le_repaid_energy
#check @M4_integral_le_repaid_window
#check @M4_integral_le_repaid_explicit
#check @M4_integral_le_1743_energy
#check @M4_integral_le_explicit
#check @lambdaTripleCount_ge_sub_M4_norm
#check @lambdaTripleCount_ge_repaid
#check @lambdaTripleCount_ge_explicit
#check @energy_fourArc
#check @minor_union_subset_source
#check @minor_energy_eq_union
#check @minor_energy_eq_source_sub_major
#check @minor_energy_le_source
#check @minor_energy_le_window
#check @minor_energy_le_sharp
#check @minor_integrals_le_weighted_energy
#check @weighted_energy_le_single_budget
#check @minor_integrals_le_max_single_budget
#check @minor_integrals_le_weighted_repaid

#print axioms continuous_S
#print axioms continuous_energy
#print axioms energy_integrableOn
#print axioms integral_S_sq
#print axioms setIntegral_S_sq
#print axioms source_energy_eq
#print axioms window_subset_Icc
#print axioms window_sq_le_prefix
#print axioms source_energy_le_mother
#print axioms source_energy_le_sharp
#print axioms set_energy_nonneg
#print axioms set_energy_le_source
#print axioms circleKernel_integrableOn
#print axioms norm_circleKernel
#print axioms norm_setIntegral_le_local_energy
#print axioms norm_setIntegral_le_source_energy
#print axioms repaid_mother_nonneg
#print axioms M4_integral_le_repaid_local_energy
#print axioms M4_integral_le_repaid_energy
#print axioms M4_integral_le_repaid_window
#print axioms M4_integral_le_repaid_explicit
#print axioms M4_integral_le_1743_energy
#print axioms M4_integral_le_explicit
#print axioms lambdaTripleCount_ge_sub_M4_norm
#print axioms lambdaTripleCount_ge_repaid
#print axioms lambdaTripleCount_ge_explicit
#print axioms energy_fourArc
#print axioms minor_union_subset_source
#print axioms minor_energy_eq_union
#print axioms minor_energy_eq_source_sub_major
#print axioms minor_energy_le_source
#print axioms minor_energy_le_window
#print axioms minor_energy_le_sharp
#print axioms minor_integrals_le_weighted_energy
#print axioms weighted_energy_le_single_budget
#print axioms minor_integrals_le_max_single_budget
#print axioms minor_integrals_le_weighted_repaid
