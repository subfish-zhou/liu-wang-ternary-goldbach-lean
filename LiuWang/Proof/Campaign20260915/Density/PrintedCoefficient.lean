import LiuWang.Proof.Campaign20260915.Density.ChenConstants

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Density

/- The English publisher scan, p.912 (48), prints this scalar comparison.
This checks only that literal comparison, not the detector mean or density bound. -/
theorem printed_english_48_scalar_incompatible {alpha : ℝ} (ha : alpha ≤ 1) :
    ¬ (1.5 * 142068 * (30.5879 : ℝ) ^ (2 : ℕ) * Real.exp (4 / 1.5)) /
        (2 * Real.pi) ≤ 186.25 * (30.5879 : ℝ) ^ alpha := by
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 30.5879) ha
  rw [Real.rpow_one] at hpow
  have he : 1 ≤ Real.exp ((4 : ℝ) / 1.5) :=
    Real.one_le_exp (by norm_num)
  apply not_le.mpr
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow (by norm_num))
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
  nlinarith [Real.pi_lt_four]

#check printed_english_48_scalar_incompatible
#print axioms printed_english_48_scalar_incompatible

end LiuWang.Proof.Campaign20260915.Density
