import LiuWang.Proof.ParameterComparisons.VaughanRange

/-! 真实自然模数的直接消费者；只使用原文规模与模数区间前提。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ParameterComparisons.VaughanRangeConsumer

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

theorem natural_modulus_bound {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    (0.28 : ℝ) * (N : ℝ) * (q : ℝ) ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤
      (0.3 : ℝ) * (N : ℝ) / sourceL N :=
  vaughan_scalar_range_nat hN hqL hqU

theorem natural_modulus_floor_bound {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : q ≤ ⌊sourceQ N⌋₊) :
    (0.28 : ℝ) * (N : ℝ) * (q : ℝ) ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤
      (0.3 : ℝ) * (N : ℝ) / sourceL N :=
  natural_modulus_bound hN hqL
    ((nat_le_floor_sourceQ_iff (exp_2000_le_of_exp_3100_le hN)).1 hqU)

end LiuWang.Proof.ParameterComparisons.VaughanRangeConsumer
