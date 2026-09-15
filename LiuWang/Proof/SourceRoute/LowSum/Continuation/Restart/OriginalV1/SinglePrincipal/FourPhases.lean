import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal.CaseIII

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

theorem caseIIIData_signed {d e q : ℕ} [NeZero d] [NeZero e] {x : ℝ}
    {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e} {rho tau upsilon : ℂ}
    (h : CaseIIIData x q chi psi rho tau upsilon) (b c : Bool) :
    CaseIIIData x q (lwdSignedCharacter chi b) (lwdSignedCharacter psi c)
      rho (lwdSignedZero tau b) (lwdSignedZero upsilon c) where
  scale_ge := h.scale_ge
  level_le := h.level_le
  chi_dvd := h.chi_dvd
  psi_dvd := h.psi_dvd
  chi_nonprincipal := lwd_signed_nonprincipal chi h.chi_nonprincipal b
  psi_nonprincipal := lwd_signed_nonprincipal psi h.psi_nonprincipal c
  chi_primitive := lwd_signed_primitive chi h.chi_primitive b
  psi_primitive := lwd_signed_primitive psi h.psi_primitive c
  rho_re := h.rho_re
  tau_re := by simpa only [lwd_signed_re] using h.tau_re
  upsilon_re := by simpa only [lwd_signed_re] using h.upsilon_re
  rho_zero := h.rho_zero
  tau_zero := lwd_signed_zero chi h.chi_nonprincipal h.tau_zero b
  upsilon_zero := lwd_signed_zero psi h.psi_nonprincipal h.upsilon_zero c
  separation := by
    have h1 := signed_separation h.separation.1 h.separation.2.1 false b
    have h2 := signed_separation h.separation.2.2.1 h.separation.2.2.2.1 false c
    have h3 := signed_separation h.separation.2.2.2.2.1 h.separation.2.2.2.2.2 b c
    exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩
  gaps := by simpa only [lwd_signed_re] using h.gaps
  heights := by simpa only [lwd_signed_height] using h.heights
  zeta_height := h.zeta_height

theorem lwd_2_28_case_iii {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    0 ≤ 1 / (lwdSourceSigma x - 1) -
      (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
        1 / (lwdSourceSigma x - upsilon.re)) +
      7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  have hbound (b c : Bool) := lwd_case_iii (caseIIIData_signed h b c) hgammaHigh hgammaLow
  have h0 := hbound false false
  have h1 := hbound true false
  have h2 := hbound false true
  have h3 := hbound true true
  simp only [lwdSignedCharacter, lwdSignedZero, Bool.false_eq_true, if_false, if_true, conj_re, conj_im]
    at h0 h1 h2 h3
  have hpos := lwd_2_13 (1 : DirichletCharacter ℂ 1) chi psi
    (lwd_source_parameters h.scale_ge).2.2.1 rho.im tau.im upsilon.im
  linarith only [hpos, h0, h1, h2, h3]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
