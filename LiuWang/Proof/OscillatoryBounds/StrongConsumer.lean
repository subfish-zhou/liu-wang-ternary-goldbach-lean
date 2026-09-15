import LiuWang.Proof.OscillatoryBounds.EndpointChecks

/-! 将已证更强常数接到原 Jrho，不放宽回原文较粗系数。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.OscillatoryBounds

open Interfaces

theorem Jrho_sqrt_ten {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) (η : ℝ) :
    ‖Jrho N rho η‖ ≤
      10 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im| := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := norm_integral_cpow_charReal_sqrt_general
    (by positivity : 0 < (N : ℝ) / 1000)
    (by linarith : (N : ℝ) / 1000 ≤ N) hbeta hgamma η
  have heq : ((N : ℝ) / 1000) ^ (rho.re - 1) * (N : ℝ) =
      (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re := by
    rw [show (N : ℝ) / 1000 = (0.001 : ℝ) * N by ring,
      Real.mul_rpow (by norm_num) hn.le, Real.rpow_sub_one hn.ne']
    field_simp
  rw [mul_assoc 10, heq] at h
  simpa only [Jrho, sourceWindowLower, mul_assoc] using h

theorem Jrho_far_three_pi {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hη : |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |η|) :
    ‖Jrho N rho η‖ ≤
      (3 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |η| := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hG : 0 < |rho.im| := abs_pos.mpr hgamma
  have hηpos : 0 < |η| := (div_pos hG (by positivity)).trans_le hη
  have hsep : 2 * |rho.im| ≤ (2 * Real.pi * |η|) * ((N : ℝ) / 1000) := by
    have h := (div_le_iff₀ (by positivity : 0 < 0.001 * Real.pi * (N : ℝ))).mp hη
    nlinarith
  have hr : rho ≠ 0 := fun h => hgamma (by simp [h])
  have h := norm_integral_cpow_charReal_far_general
    (by positivity : 0 < (N : ℝ) / 1000) (by linarith : (N : ℝ) / 1000 ≤ N)
    hr hbeta (abs_pos.mp hηpos) hsep
  apply h.trans_eq
  rw [show (N : ℝ) / 1000 = (0.001 : ℝ) * N by ring]
  field_simp
  ring

end LiuWang.Proof.OscillatoryBounds
