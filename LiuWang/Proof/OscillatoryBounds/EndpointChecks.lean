import LiuWang.Proof.OscillatoryBounds.Consumer

/-! # 零频与两条交界线的原积分检查 -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.OscillatoryBounds

theorem J_zero_value (N : ℕ) :
    J N 0 = ((0.999 * (N : ℝ) : ℝ) : ℂ) := by
  simp [J, sourceWindowLower, charReal]
  ring

theorem source_thresholds_order {N : ℝ} (hN : 0 < N) (gamma : ℝ) :
    |gamma| / (10 * Real.pi * N) ≤ |gamma| / (0.001 * Real.pi * N) := by
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  nlinarith [Real.pi_pos]

theorem Jrho_lower_boundary {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : 0 ≤ rho.re) (hbeta1 : rho.re ≤ 1) (hgamma : rho.im ≠ 0)
    {ε : ℝ} (hε : |ε| = 1) :
    ‖Jrho N rho (ε * (|rho.im| / (10 * Real.pi * (N : ℝ))))‖ ≤
      min (5 * (N : ℝ) ^ rho.re / |rho.im|)
        (16 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im|) := by
  have heq : |ε * (|rho.im| / (10 * Real.pi * (N : ℝ)))| =
      |rho.im| / (10 * Real.pi * (N : ℝ)) := by
    rw [abs_mul, hε, one_mul, abs_of_nonneg (by positivity)]
  apply le_min
  · exact Jrho_near hN hbeta hgamma (by rw [heq])
  · exact Jrho_transition hN hbeta1 hgamma (by rw [heq])
      (by rw [heq]; exact source_thresholds_order (by exact_mod_cast hN) rho.im)

theorem Jrho_upper_boundary {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0)
    {ε : ℝ} (hε : |ε| = 1) :
    ‖Jrho N rho (ε * (|rho.im| / (0.001 * Real.pi * (N : ℝ))))‖ ≤
      min (16 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im|)
        ((4 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) /
          |ε * (|rho.im| / (0.001 * Real.pi * (N : ℝ)))|) := by
  have heq : |ε * (|rho.im| / (0.001 * Real.pi * (N : ℝ)))| =
      |rho.im| / (0.001 * Real.pi * (N : ℝ)) := by
    rw [abs_mul, hε, one_mul, abs_of_nonneg (by positivity)]
  apply le_min
  · exact Jrho_transition hN hbeta hgamma
      (by rw [heq]; exact source_thresholds_order (by exact_mod_cast hN) rho.im)
      (by rw [heq])
  · exact Jrho_far hN hbeta hgamma (by rw [heq])

end LiuWang.Proof.OscillatoryBounds
