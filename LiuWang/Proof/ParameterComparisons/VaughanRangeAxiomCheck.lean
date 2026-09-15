import LiuWang.Proof.ParameterComparisons.VaughanRangeConsumer

/-! 输出全部新增定理的完整类型与传递公理依赖。 -/

set_option pp.fullNames true
set_option pp.universes true

open LiuWang.Proof.ParameterComparisons

#check @sourceL_eighth_lt_natCast_half
#print axioms sourceL_eighth_lt_natCast_half
#check @sourceL_thirteen_halves_ratio_le
#print axioms sourceL_thirteen_halves_ratio_le
#check @sourceL_twelve_fifths_small
#print axioms sourceL_twelve_fifths_small
#check @vaughan_middle_term_le
#print axioms vaughan_middle_term_le
#check @vaughan_normalized_pair_le
#print axioms vaughan_normalized_pair_le
#check @vaughan_variable_pair_le
#print axioms vaughan_variable_pair_le
#check @vaughan_scalar_range_margin
#print axioms vaughan_scalar_range_margin
#check @vaughan_scalar_range
#print axioms vaughan_scalar_range
#check @vaughan_scalar_range_nat
#print axioms vaughan_scalar_range_nat
#check @VaughanRangeConsumer.natural_modulus_bound
#print axioms VaughanRangeConsumer.natural_modulus_bound
#check @VaughanRangeConsumer.natural_modulus_floor_bound
#print axioms VaughanRangeConsumer.natural_modulus_floor_bound
