import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal.CaseI

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal

theorem caseIData_signed {q : ℕ} {x : ℝ} {rho tau upsilon : ℂ}
    (h : CaseIData x q rho tau upsilon) (b c : Bool) :
    CaseIData x q rho (lwdSignedZero tau b) (lwdSignedZero upsilon c) where
  scale_ge := h.scale_ge
  level_le := h.level_le
  rho_re := h.rho_re
  tau_re := by simpa only [lwd_signed_re] using h.tau_re
  upsilon_re := by simpa only [lwd_signed_re] using h.upsilon_re
  rho_zero := h.rho_zero
  tau_zero := by
    cases b
    · exact h.tau_zero
    · simpa only [lwdSignedZero, if_true, riemannZeta_conj, map_zero] using congrArg conj h.tau_zero
  upsilon_zero := by
    cases c
    · exact h.upsilon_zero
    · simpa only [lwdSignedZero, if_true, riemannZeta_conj, map_zero] using congrArg conj h.upsilon_zero
  separation := by
    have h1 := signed_separation h.separation.1 h.separation.2.1 false b
    have h2 := signed_separation h.separation.2.2.1 h.separation.2.2.2.1 false c
    have h3 := signed_separation h.separation.2.2.2.2.1 h.separation.2.2.2.2.2 b c
    exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩
  gaps := by simpa only [lwd_signed_re] using h.gaps
  heights := by simpa only [lwd_signed_height] using h.heights
  zeta_heights := by simpa only [lwd_signed_height] using h.zeta_heights

theorem lwd_2_28_case_i {q : ℕ} [NeZero q] {x : ℝ} {rho tau upsilon : ℂ}
    (h : CaseIData x q rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    0 ≤ 1 / (lwdSourceSigma x - 1) -
      (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
        1 / (lwdSourceSigma x - upsilon.re)) +
      7 * stechkinConductorCoeff * Real.log x + 0.0876 := by
  have hbound (b c : Bool) := lwd_case_i (caseIData_signed h b c) hgammaHigh hgammaLow
  have h0 := hbound false false
  have h1 := hbound true false
  have h2 := hbound false true
  have h3 := hbound true true
  simp only [lwdSignedZero, Bool.false_eq_true, if_false, if_true, conj_re, conj_im] at h0 h1 h2 h3
  have hpos := lwd_2_13 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
    (1 : DirichletCharacter ℂ 1) (lwd_source_parameters h.scale_ge).2.2.1 rho.im tau.im upsilon.im
  simp only [inv_one] at hpos
  linarith only [hpos, h0, h1, h2, h3]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal
