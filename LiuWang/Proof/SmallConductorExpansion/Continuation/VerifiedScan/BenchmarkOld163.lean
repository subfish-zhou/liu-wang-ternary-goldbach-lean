import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Prefix
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163

/-! # Fresh kernel replay of the unchanged old 163 certificate for comparison -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

theorem old163_replay : RationalWeightedCertificate 163 values163 163 9 (127 / 125) := by
  constructor <;> decide +kernel

theorem old163_original_region (chi : DirichletCharacter ℂ 163)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 163 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rw [quadratic_prime_eq 163 (by decide) chi hc hsq]
  apply rationalWeighted_original_region (primeCharacter 163)
    (primeCharacter_ne_one 163 (by decide)) values163 table163
    (by decide) (dvd_refl 163) (n := 46) (by decide) old163_replay
    (by norm_num) (by norm_num) _ hb
  exact log_scale_fortysix (by linarith)

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
