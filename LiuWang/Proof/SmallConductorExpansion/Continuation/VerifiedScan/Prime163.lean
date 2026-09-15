import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Prefix
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163

/-! # The original 163 input, paid again by the verified scan -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

theorem scan163 : Weighted 163 values163 163 9 (127 / 125) := by
  unfold Weighted
  constructor <;> decide +kernel

theorem certificate163_scan : RationalWeightedCertificate 163 values163 163 9 (127 / 125) :=
  (weighted_iff _ _ _ _ _).mp scan163

theorem scan163_original_region (chi : DirichletCharacter ℂ 163)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 163 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rw [quadratic_prime_eq 163 (by decide) chi hc hsq]
  apply rationalWeighted_original_region (primeCharacter 163)
    (primeCharacter_ne_one 163 (by decide)) values163 table163
    (by decide) (dvd_refl 163) (n := 46) (by decide) certificate163_scan
    (by norm_num) (by norm_num) _ hb
  exact log_scale_fortysix (by linarith)

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
