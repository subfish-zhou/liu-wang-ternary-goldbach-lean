import LiuWang.Proof.Campaign20260915.RSSection8Scalar.LogTail

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.RSSection8Scalar

/-- The explicit prime-power envelope integrated in RS1962, p.86. -/
def primePowerIntegrand (y : ℝ) : ℝ :=
  ((1.02 : ℝ) * y ^ (1 / 2 : ℝ) + 3 * y ^ (1 / 3 : ℝ)) *
    (1 + Real.log y) / (y ^ 2 * Real.log y ^ 2)

theorem primePowerIntegrand_eq {y : ℝ} (hy : 0 < y) :
    primePowerIntegrand y =
      1.02 * logTailKernel (1 / 2) 1 y + 3 * logTailKernel (1 / 3) 1 y := by
  have hp (a : ℝ) : y ^ (a - 1 - 1) = y ^ a / y ^ 2 := by
    rw [show a - 1 - 1 = a - (2 : ℝ) by ring, Real.rpow_sub hy,
      Real.rpow_two]
  unfold primePowerIntegrand logTailKernel
  rw [hp, hp]
  ring

theorem primePowerIntegrand_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn primePowerIntegrand (Ioi x) := by
  have hi := ((logTailKernel_integrable (a := 1 / 2) (n := 1)
    (by norm_num) (by norm_num) hx).const_mul 1.02).add
      ((logTailKernel_integrable (a := 1 / 3) (n := 1)
        (by norm_num) (by norm_num) hx).const_mul 3)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (primePowerIntegrand_eq (by linarith [show x < y from hy])).symm

theorem primePower_integral_le {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, primePowerIntegrand y) ≤
      (2.04 / x ^ (1 / 2 : ℝ) + 4.5 * x ^ (-2 / 3 : ℝ)) / Real.log x := by
  have hhalf := lemma9 (a := 1 / 2) (n := 1) (by norm_num) (by norm_num) hx
  have hthird := lemma9 (a := 1 / 3) (n := 1) (by norm_num) (by norm_num) hx
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 1.02))
    (mul_le_mul_of_nonneg_left hthird (by norm_num : (0 : ℝ) ≤ 3))
  have he : (∫ y in Ioi x, primePowerIntegrand y) =
      1.02 * (∫ y in Ioi x, logTailKernel (1 / 2) 1 y) +
        3 * (∫ y in Ioi x, logTailKernel (1 / 3) 1 y) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact primePowerIntegrand_eq (by linarith [show x < y from hy])
    · exact (logTailKernel_integrable (by norm_num) (by norm_num) hx).const_mul _
    · exact (logTailKernel_integrable (by norm_num) (by norm_num) hx).const_mul _
  rw [he]
  convert! hsum using 1
  norm_num
  rw [Real.rpow_neg (by linarith : 0 ≤ x) (1 / 2)]
  ring

#print axioms primePowerIntegrand_integrable
#print axioms primePower_integral_le

end LiuWang.Proof.Campaign20260915.RSSection8Scalar
