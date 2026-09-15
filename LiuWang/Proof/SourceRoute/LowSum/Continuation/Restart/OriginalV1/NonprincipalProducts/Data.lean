import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.Selection

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

structure TripleData {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f] (x : ℝ) (q : ℕ)
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (rho tau upsilon : ℂ) : Prop where
  scale_ge : 8000000000 ≤ x
  level_le : (q : ℝ) ≤ x
  chi_dvd : d ∣ q
  psi_dvd : e ∣ q
  eta_dvd : f ∣ q
  chi_nonprincipal : chi ≠ 1
  psi_nonprincipal : psi ≠ 1
  eta_nonprincipal : eta ≠ 1
  chi_primitive : chi.IsPrimitive
  psi_primitive : psi.IsPrimitive
  eta_primitive : eta.IsPrimitive
  rho_re : 1 / 2 < rho.re ∧ rho.re < 1
  tau_re : 1 / 2 < tau.re ∧ tau.re < 1
  upsilon_re : 1 / 2 < upsilon.re ∧ upsilon.re < 1
  rho_zero : chi.LFunction rho = 0
  tau_zero : psi.LFunction tau = 0
  upsilon_zero : eta.LFunction upsilon = 0
  separation : rho ≠ tau ∧ rho ≠ conj tau ∧
    rho ≠ upsilon ∧ rho ≠ conj upsilon ∧ tau ≠ upsilon ∧ tau ≠ conj upsilon
  gaps : 1 - rho.re ≤ lwdSourceSigma x - 1 ∧
    1 - tau.re ≤ lwdSourceSigma x - 1 ∧ 1 - upsilon.re ≤ lwdSourceSigma x - 1
  heights : |rho.im| ≤ x / q ∧ |tau.im| ≤ x / q ∧ |upsilon.im| ≤ x / q

def pairCount {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) : ℕ :=
  (if lwdProduct chi psi = 1 then 1 else 0) +
  (if lwdProduct chi eta = 1 then 1 else 0) +
  (if lwdProduct psi eta = 1 then 1 else 0)

theorem pairCount_le_three {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) :
    pairCount chi psi eta ≤ 3 := by
  unfold pairCount
  split_ifs <;> norm_num

theorem conjugate_separation {rho tau : ℂ} (h : rho ≠ conj tau) : tau ≠ conj rho := by
  intro he
  exact h (by simpa using (congrArg conj he).symm)

theorem pair_cost {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    {x sigma t u beta eta : ℝ} (hd : d ∣ q) (he : e ∣ q) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    (ht : |t| ≤ x / q) (hu : |u| ≤ x / q)
    (hb : beta < 1) (he' : eta < 1)
    (hgb : 1 - beta ≤ sigma - 1) (hge : 1 - eta ≤ sigma - 1)
    (hgammaHigh : ∀ v : ℝ, 1 ≤ |v| →
      gammaHalfDifference sigma v < stechkinConductorCoeff * Real.log |v| + 0.3316)
    (hgammaLow : ∀ v : ℝ, |v| < 1 → gammaHalfDifference sigma v < 0.0615) :
    dampedLogDeriv (lwdProduct chi psi) sigma (stechkinSigma sigma) stechkinK (t + u) -
      (if lwdProduct chi psi = 1 then poleDebit sigma beta (t + u) else 0) -
      (if lwdProduct chi psi = 1 then poleDebit sigma eta (t + u) else 0) ≤
      nonprincipalCost (2 * x) + 0.4977 -
      (if lwdProduct chi psi = 1 then 0.0602 else 0) := by
  have hx : 0 < x := (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q).trans_le hq
  by_cases hp : lwdProduct chi psi = 1
  · have htu : |t + u| ≤ (2 * x) / q := by
      rw [mul_div_assoc]
      linarith [abs_add_le t u]
    have hh := principal_pair_paid (Nat.lcm_dvd hd he) hs hs1
      (show (q : ℝ) ≤ 2 * x by linarith) htu hb he' hgb hge hgammaHigh hgammaLow
    simp only [hp, if_true]
    unfold nonprincipalCost AllPrincipal.principalCost at *
    linarith
  · have hh := lwd_2_25 (Nat.lcm_dvd hd he) hq (lwdProduct chi psi) hp ht hu hs (by linarith)
    simp only [if_neg hp, sub_zero, nonprincipalCost]
    rw [Real.log_mul (by norm_num) hx.ne']
    nlinarith only [hh]

theorem original_product_constants :
    (-0.8973 + 7 * 0.3918 + 4 * 0.4977 +
      stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) -
      0.0602 ≤ 2.4396) ∧
    (-0.8973 + 7 * 0.3918 + 4 * 0.4977 +
      stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) -
      2 * 0.0602 ≤ 2.3795) ∧
    (-0.8973 + 7 * 0.3918 + 4 * 0.4977 +
      stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) -
      3 * 0.0602 ≤ 2.3193) := by
  exact ⟨by linarith [lwd_2_27_constant], by linarith [lwd_2_27_constant],
    by linarith [lwd_2_27_constant]⟩

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
