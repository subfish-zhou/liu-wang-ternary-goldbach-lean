import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.Scalar
import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.FiniteCertificates

set_option autoImplicit false

noncomputable section

open Finset

namespace LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

theorem higherPrimePowers_lt_three {x : ℝ} (hx : 0 < x) :
    higherPrimePowers x < 3 * x ^ (1 / (3 : ℝ)) := by
  by_cases hsmall : x < 65536
  · exact higherPrimePowers_lt_three_small hx hsmall
  by_cases hmiddle : x < 16777216
  · have hroot : x ^ (1 / (3 : ℝ)) ≤ 256 := by
      rw [one_div, Real.rpow_inv_le_iff_of_pos hx.le (by norm_num) (by norm_num)]
      norm_num
      exact hmiddle.le
    have hcut : ⌊Real.log x / Real.log 2⌋₊ ≤ 24 :=
      log_cutoff_of_lt_pow_two hx (by norm_num; linarith)
    exact (higherPrimePowers_le_local_sum (by linarith : 1 ≤ x) hroot
      (fun _ hy hy256 => theta_le_self_up_to_256 hy hy256)
      (by norm_num : 2 ≤ 24) hcut).trans_lt
        (middle_sum_lt_three (le_of_not_gt hsmall))
  have hN2 : 2 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (by linarith : (4 : ℝ) ≤ x)
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at h
    norm_num at h ⊢
    exact h
  exact (higherPrimePowers_le_elementary_sum hx.le hN2 le_rfl).trans_lt
    (elementary_sum_lt_three (le_of_not_gt hmiddle))

/-- Rosser--Schoenfeld (1962), (3.38), without a global effective theta hypothesis. -/
theorem equation_3_38 {x : ℝ} (hx : 0 < x) :
    Chebyshev.psi x - Chebyshev.theta x <
      Chebyshev.theta (Real.sqrt x) + 3 * x ^ (1 / (3 : ℝ)) := by
  have h := higherPrimePowers_lt_three hx
  unfold higherPrimePowers at h
  linarith

theorem psi_sub_theta_lt_elementary {x : ℝ} (hx : 0 < x) :
    Chebyshev.psi x - Chebyshev.theta x <
      Real.log 4 * Real.sqrt x + 3 * x ^ (1 / (3 : ℝ)) := by
  have hs := Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg x)
  have h := equation_3_38 hx
  linarith

/-- The only numerical input here is the finite upper half of Theorem 18. -/
theorem equation_4_12_of_finite_theta
    (htheta : ∀ y : ℝ, 0 < y → y ≤ 100000000 → Chebyshev.theta y ≤ y)
    {x : ℝ} (hx : 0 < x) (hxB : x ≤ 10000000000000000) :
    Chebyshev.psi x - Chebyshev.theta x <
      Real.sqrt x + 3 * x ^ (1 / (3 : ℝ)) := by
  have hsB : Real.sqrt x ≤ 100000000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hs := htheta (Real.sqrt x) (Real.sqrt_pos.mpr hx) hsB
  have h := equation_3_38 hx
  linarith

theorem theta_bounds_of_psi_bounds_raw {x L U : ℝ} (hx : 0 < x)
    (hL : L ≤ Chebyshev.psi x) (hU : Chebyshev.psi x ≤ U) :
    L - Real.log 4 * Real.sqrt x - 3 * x ^ (1 / (3 : ℝ)) <
      Chebyshev.theta x ∧ Chebyshev.theta x ≤ U := by
  constructor
  · have h := psi_sub_theta_lt_elementary hx
    linarith
  · exact (Chebyshev.theta_le_psi x).trans hU

theorem theta_bounds_of_psi_bounds_finite
    (htheta : ∀ y : ℝ, 0 < y → y ≤ 100000000 → Chebyshev.theta y ≤ y)
    {x L U : ℝ} (hx : 0 < x) (hxB : x ≤ 10000000000000000)
    (hL : L ≤ Chebyshev.psi x) (hU : Chebyshev.psi x ≤ U) :
    L - Real.sqrt x - 3 * x ^ (1 / (3 : ℝ)) <
      Chebyshev.theta x ∧ Chebyshev.theta x ≤ U := by
  constructor
  · have h := equation_4_12_of_finite_theta htheta hx hxB
    linarith
  · exact (Chebyshev.theta_le_psi x).trans hU

#print axioms higherPrimePowers_lt_three
#print axioms equation_3_38
#print axioms psi_sub_theta_lt_elementary
#print axioms equation_4_12_of_finite_theta
#print axioms theta_bounds_of_psi_bounds_raw
#print axioms theta_bounds_of_psi_bounds_finite

end LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections
