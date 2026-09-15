import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.SpectralReserves
import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.Main

/-! Effective-tail components and the actual prime-power correction.
The selected-cutoff numerical zero tail and low-window verification are not proved here.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LiuWang.Proof.Campaign20260915.Parent.EffectiveTailAudit
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem actual_prime_power_correction_reserve {x : ℝ} (hx : 0 < x)
    (hL : 5000 ≤ Real.log x) :
    1.84 + (Chebyshev.psi x - Chebyshev.theta x) + rsTrivialKernel x <
      x * epsilon x / 8 := by
  have hc := elementary_correction_reserve hx hL
  have hp := LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.psi_sub_theta_lt_elementary hx
  linarith

#print axioms actual_prime_power_correction_reserve
end LiuWang.Proof.Campaign20260915.Parent.EffectiveTailAudit

#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.saddle_sq
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.saddle_ge_sixteen
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.log_spectralCutoff
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.spectralCutoff_ge_rsA
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.spectralCutoff_exact_domain
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.spectralCutoff_theorem27_domain
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.cubic_exp_tail
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.log_mul_epsilon_le
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.epsilon_lt_half_log_inv
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.phi_one_exp
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.phi_one_peak
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.actual_high_term_le_peak
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.actual_finite_spectrum_le_peak
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.saddle_outer_integral
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.saddle_laplace_le
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.saddle_integral
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.phi_integral_selected_cutoff
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.Q_phi_integral_selected_cutoff
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.saddle_exp_small
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.smoothingStep_bounds
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.smoothingStep_cut
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.smoothingStep_moment_budget
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.smoothing_epsilon_small
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.original_epsilon_lower
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.smoothing_epsilon_reserve
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.integral_budget_reserve
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.actual_high_spectrum_split
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.actual_selected_high_spectrum
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.trivialKernel_le_inv_sq
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.half_log_ge_saddle
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.exponential_correction_reserve
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.elementary_correction_reserve
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.selected_cutoff_ge_ten_thousand
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.selected_window_card_le
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.selected_window_peak_budget
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.actual_middle_spectrum_budget
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.actual_high_spectrum_after_middle
#print axioms LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.weighted_first_moment_budget
