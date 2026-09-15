import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q65
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q66
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q68
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q69
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q70
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q71
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q72
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q73
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q74
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q75
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q76
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q77
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q78
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q79
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Q80

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

theorem batch65_80 {q : ℕ} [NeZero q] (hlo : 65 ≤ q) (hhi : q ≤ 80)
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have he : q = 65 ∨ q = 66 ∨ q = 67 ∨ q = 68 ∨ q = 69 ∨ q = 70 ∨ q = 71 ∨ q = 72 ∨ q = 73 ∨ q = 74 ∨ q = 75 ∨ q = 76 ∨ q = 77 ∨ q = 78 ∨ q = 79 ∨ q = 80 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact level65 chi hc hsq hqx hb
  · exact level66 chi hc hsq hqx hb
  · exact quadratic_67_original_region chi hc hsq hqx hb
  · exact level68 chi hc hsq hqx hb
  · exact level69 chi hc hsq hqx hb
  · exact level70 chi hc hsq hqx hb
  · exact level71 chi hc hsq hqx hb
  · exact level72 chi hc hsq hqx hb
  · exact level73 chi hc hsq hqx hb
  · exact level74 chi hc hsq hqx hb
  · exact level75 chi hc hsq hqx hb
  · exact level76 chi hc hsq hqx hb
  · exact level77 chi hc hsq hqx hb
  · exact level78 chi hc hsq hqx hb
  · exact level79 chi hc hsq hqx hb
  · exact level80 chi hc hsq hqx hb

theorem ordinary_batch65_80
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (hc : 65 ≤ chi.conductor ∧ chi.conductor ≤ 80) {rho : ℂ}
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  apply ordinary_of_level_coverage (fun r => 65 ≤ r ∧ r ≤ 80) _ hx hq chi hc hr ht hp
  intro r _ h psi hpsi hs x beta _ hrx hb
  exact batch65_80 h.1 h.2 psi hpsi hs hrx hb

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
