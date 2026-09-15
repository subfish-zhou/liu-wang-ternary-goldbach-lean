import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.TripleCase

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

theorem pairCount_zero_iff {d e f : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) :
    pairCount chi psi eta = 0 ↔
      lwdProduct chi psi ≠ 1 ∧ lwdProduct chi eta ≠ 1 ∧ lwdProduct psi eta ≠ 1 := by
  unfold pairCount
  split_ifs <;> simp_all

theorem actual_case_exhaustion {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon) :
    (pairCount chi psi eta = 0 ∧ lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
      (pairCount chi psi eta = 1 ∧ lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
      (pairCount chi psi eta = 2 ∧ lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
      (pairCount chi psi eta = 3 ∧ lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
      (pairCount chi psi eta = 0 ∧ lwdProduct (lwdProduct chi psi) eta = 1) := by
  by_cases ht : lwdProduct (lwdProduct chi psi) eta = 1
  · have hp := triple_principal_no_pair chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd
      h.chi_nonprincipal h.psi_nonprincipal h.eta_nonprincipal ht
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(pairCount_zero_iff chi psi eta).mpr hp, ht⟩)))
  · have hh := pairCount_le_three chi psi eta
    have hn : pairCount chi psi eta = 0 ∨ pairCount chi psi eta = 1 ∨
        pairCount chi psi eta = 2 ∨ pairCount chi psi eta = 3 := by omega
    rcases hn with hn | hn | hn | hn
    · exact Or.inl ⟨hn, ht⟩
    · exact Or.inr (Or.inl ⟨hn, ht⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hn, ht⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, ht⟩)))

theorem pairCount_one_iff {d e f : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) :
    pairCount chi psi eta = 1 ↔
      (lwdProduct chi psi = 1 ∧ lwdProduct chi eta ≠ 1 ∧ lwdProduct psi eta ≠ 1) ∨
      (lwdProduct chi psi ≠ 1 ∧ lwdProduct chi eta = 1 ∧ lwdProduct psi eta ≠ 1) ∨
      (lwdProduct chi psi ≠ 1 ∧ lwdProduct chi eta ≠ 1 ∧ lwdProduct psi eta = 1) := by
  unfold pairCount
  split_ifs <;> simp_all

theorem pairCount_two_iff {d e f : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) :
    pairCount chi psi eta = 2 ↔
      (lwdProduct chi psi = 1 ∧ lwdProduct chi eta = 1 ∧ lwdProduct psi eta ≠ 1) ∨
      (lwdProduct chi psi = 1 ∧ lwdProduct chi eta ≠ 1 ∧ lwdProduct psi eta = 1) ∨
      (lwdProduct chi psi ≠ 1 ∧ lwdProduct chi eta = 1 ∧ lwdProduct psi eta = 1) := by
  unfold pairCount
  split_ifs <;> simp_all

theorem pairCount_three_iff {d e f : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) :
    pairCount chi psi eta = 3 ↔
      lwdProduct chi psi = 1 ∧ lwdProduct chi eta = 1 ∧ lwdProduct psi eta = 1 := by
  unfold pairCount
  split_ifs <;> simp_all

theorem lwd_all_nonprincipal {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  rcases actual_case_exhaustion h with h0 | h1 | h2 | h3 | ht
  · have hp := (pairCount_zero_iff chi psi eta).mp h0.1
    exact lwd_2_27_case_iv h.scale_ge h.level_le h.chi_dvd h.psi_dvd h.eta_dvd chi psi eta
      h.chi_nonprincipal h.psi_nonprincipal h.eta_nonprincipal h.chi_primitive h.psi_primitive h.eta_primitive
      hp.1 hp.2.1 hp.2.2 h0.2 h.rho_re.1 h.rho_re.2 h.rho_zero h.tau_re.1 h.tau_re.2 h.tau_zero
      h.upsilon_re.1 h.upsilon_re.2 h.upsilon_zero h.heights.1 h.heights.2.1 h.heights.2.2
  · linarith only [lwd_case_v h h1.1 hgammaHigh hgammaLow]
  · linarith only [lwd_case_vi h h2.1 hgammaHigh hgammaLow]
  · linarith only [lwd_case_vii h h3.1 hgammaHigh hgammaLow]
  · linarith only [lwd_case_viii h ht.2 hgammaHigh hgammaLow]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
