import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.PairCases
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.Induction

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

theorem lwd_case_viii {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon)
    (htriple : lwdProduct (lwdProduct chi psi) eta = 1)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4397 := by
  have hx : 0 < x := by linarith [h.scale_ge]
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have hn := triple_principal_no_pair chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd
    h.chi_nonprincipal h.psi_nonprincipal h.eta_nonprincipal htriple
  have ht13 : lwdProduct (lwdProduct chi eta) psi = 1 := by
    apply (triple_principal_iff chi eta psi h.chi_dvd h.eta_dvd h.psi_dvd).mpr
    have hh := (triple_principal_iff chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd).mp htriple
    rwa [mul_right_comm] at hh
  let : NeZero (lwdProduct chi psi).conductor := ⟨(lwdProduct chi psi).conductor_ne_zero⟩
  let : NeZero (lwdProduct chi eta).conductor := ⟨(lwdProduct chi eta).conductor_ne_zero⟩
  have hz12 := triple_pair_zero chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd
    h.eta_nonprincipal h.eta_primitive htriple h.upsilon_zero
  have hz13 := triple_pair_zero chi eta psi h.chi_dvd h.eta_dvd h.psi_dvd
    h.psi_nonprincipal h.psi_primitive ht13 h.tau_zero
  have hy12 : |rho.im + tau.im| ≤ (2 * x) / q := by
    rw [mul_div_assoc]
    linarith [abs_add_le rho.im tau.im, h.heights.1, h.heights.2.1]
  have hy13 : |rho.im + upsilon.im| ≤ (2 * x) / q := by
    rw [mul_div_assoc]
    linarith [abs_add_le rho.im upsilon.im, h.heights.1, h.heights.2.2]
  have hy123 : |rho.im + tau.im + upsilon.im| ≤ (3 * x) / q := by
    rw [mul_div_assoc] at hy12 ⊢
    linarith [abs_add_le (rho.im + tau.im) upsilon.im, h.heights.2.2]
  have hq2 : (q : ℝ) ≤ 2 * x := by linarith [h.level_le]
  have hq3 : (q : ℝ) ≤ 3 * x := by linarith [h.level_le]
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  have h1 := lwd_2_24 h.chi_dvd h.level_le chi h.chi_nonprincipal h.chi_primitive
    h.rho_re.1 h.rho_re.2 h.rho_zero h.heights.1 hs.1 hs1
  have h2 := lwd_2_24 h.psi_dvd h.level_le psi h.psi_nonprincipal h.psi_primitive
    h.tau_re.1 h.tau_re.2 h.tau_zero h.heights.2.1 hs.1 hs1
  have h3 := lwd_2_24 h.eta_dvd h.level_le eta h.eta_nonprincipal h.eta_primitive
    h.upsilon_re.1 h.upsilon_re.2 h.upsilon_zero h.heights.2.2 hs.1 hs1
  have h4 := imprimitive_one_debit (lwdProduct chi psi) hn.1
    (Nat.lcm_dvd h.chi_dvd h.psi_dvd) hq2 hs.1 hs.2 hy12
    (by simpa only [conj_re] using h.upsilon_re) (by simpa only [conj_re] using h.gaps.2.2) hz12
  have h5 := imprimitive_one_debit (lwdProduct chi eta) hn.2.1
    (Nat.lcm_dvd h.chi_dvd h.eta_dvd) hq2 hs.1 hs.2 hy13
    (by simpa only [conj_re] using h.tau_re) (by simpa only [conj_re] using h.gaps.2.1) hz13
  simp only [conj_re, conj_im, sub_neg_eq_add] at h4 h5
  rw [add_right_comm rho.im upsilon.im tau.im] at h5
  have h6 := lwd_2_25 (Nat.lcm_dvd h.psi_dvd h.eta_dvd) h.level_le (lwdProduct psi eta)
    hn.2.2 h.heights.2.1 h.heights.2.2 hs.1 hs1
  have h7 := principal_pair_paid (Nat.lcm_dvd (Nat.lcm_dvd h.chi_dvd h.psi_dvd) h.eta_dvd)
    hs.1 hs.2 hq3 hy123 h.upsilon_re.2 h.tau_re.2 h.gaps.2.2 h.gaps.2.1 hgammaHigh hgammaLow
  rw [← htriple] at h7
  unfold nonprincipalCost at h4 h5
  unfold AllPrincipal.principalCost at h7
  rw [Real.log_mul (by norm_num) hx.ne'] at h4 h5 h7
  unfold lwdG
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, lwd_2_27_constant]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
