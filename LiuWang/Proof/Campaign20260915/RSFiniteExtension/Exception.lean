import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Start

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
noncomputable section

theorem theta_theorem18_lower_exception {x : ℝ}
    (hx : 1420 ≤ x) (hi : x ≤ 1423) :
    x - 2.05282 * Real.sqrt x < Chebyshev.theta x := by
  let t : ℝ := (13455622264421 : ℝ) / 10000000000
  have hnum : (1423 - t) ^ 2 < (2.05282 : ℝ) ^ 2 * 1423 := by
    norm_num [t]
  have hsx := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hsb := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1423)
  have hsm := Real.sqrt_le_sqrt hi
  have hsl : 2 ≤ Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  have hmain : 1423 - 2.05282 * Real.sqrt 1423 < t := by
    nlinarith [sq_nonneg (1423 - t + 2.05282 * Real.sqrt 1423)]
  have hmono : x - 2.05282 * Real.sqrt x ≤
      1423 - 2.05282 * Real.sqrt 1423 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsm)
      (show 0 ≤ Real.sqrt x + Real.sqrt 1423 - 2.05282 by linarith)]
  exact (hmono.trans_lt hmain).trans_le
    (state_1420.1.trans (Chebyshev.theta_mono hx))

#print axioms theta_theorem18_lower_exception

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
