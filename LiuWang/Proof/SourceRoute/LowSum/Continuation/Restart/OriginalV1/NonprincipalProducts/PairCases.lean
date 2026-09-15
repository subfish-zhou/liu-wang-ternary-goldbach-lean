import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.Data
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.Products

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

theorem positive_pairCount_triple_nonprincipal {d e f q : ℕ}
    [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon) (hn : 0 < pairCount chi psi eta) :
    lwdProduct (lwdProduct chi psi) eta ≠ 1 := by
  intro ht
  have hh := triple_principal_no_pair chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd
    h.chi_nonprincipal h.psi_nonprincipal h.eta_nonprincipal ht
  simp only [pairCount, if_neg hh.1, if_neg hh.2.1, if_neg hh.2.2] at hn
  omega

theorem pair_cases_account {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon)
    (htriple : lwdProduct (lwdProduct chi psi) eta ≠ 1)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x +
        (-0.8973 + 7 * 0.3918 + 4 * 0.4977 +
          stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi)) -
        0.0602 * pairCount chi psi eta := by
  have hx : 0 < x := by linarith [h.scale_ge]
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hz12 (hm : lwdProduct chi psi = 1) := principal_product_conjugate_zeros chi psi
    h.chi_nonprincipal h.psi_nonprincipal h.chi_primitive h.psi_primitive hm h.rho_zero h.tau_zero
  have hz13 (hm : lwdProduct chi eta = 1) := principal_product_conjugate_zeros chi eta
    h.chi_nonprincipal h.eta_nonprincipal h.chi_primitive h.eta_primitive hm h.rho_zero h.upsilon_zero
  have hz23 (hm : lwdProduct psi eta = 1) := principal_product_conjugate_zeros psi eta
    h.psi_nonprincipal h.eta_nonprincipal h.psi_primitive h.eta_primitive hm h.tau_zero h.upsilon_zero
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  have h1 := primitive_two_debits chi h.chi_nonprincipal h.chi_primitive h.chi_dvd h.level_le
    hs.1 hs.2 h.rho_re h.tau_re h.upsilon_re h.rho_zero h.heights.1
    h.separation.2.1 h.separation.2.2.2.1 h.separation.2.2.2.2.1 h.gaps.2.1 h.gaps.2.2
    (lwdProduct chi psi = 1) (lwdProduct chi eta = 1) (fun hm => (hz12 hm).1) (fun hm => (hz13 hm).1)
  have h2 := primitive_two_debits psi h.psi_nonprincipal h.psi_primitive h.psi_dvd h.level_le
    hs.1 hs.2 h.tau_re h.rho_re h.upsilon_re h.tau_zero h.heights.2.1
    (conjugate_separation h.separation.2.1) h.separation.2.2.2.2.2 h.separation.2.2.1
    h.gaps.1 h.gaps.2.2 (lwdProduct chi psi = 1) (lwdProduct psi eta = 1)
    (fun hm => (hz12 hm).2) (fun hm => (hz23 hm).1)
  have h3 := primitive_two_debits eta h.eta_nonprincipal h.eta_primitive h.eta_dvd h.level_le
    hs.1 hs.2 h.upsilon_re h.rho_re h.tau_re h.upsilon_zero h.heights.2.2
    (conjugate_separation h.separation.2.2.2.1) (conjugate_separation h.separation.2.2.2.2.2)
    h.separation.1 h.gaps.1 h.gaps.2.1 (lwdProduct chi eta = 1) (lwdProduct psi eta = 1)
    (fun hm => (hz13 hm).2) (fun hm => (hz23 hm).2)
  rw [add_comm tau.im rho.im] at h2
  rw [add_comm upsilon.im rho.im, add_comm upsilon.im tau.im] at h3
  have h4 := pair_cost chi psi h.chi_dvd h.psi_dvd h.level_le hs.1 hs.2 h.heights.1 h.heights.2.1
    h.rho_re.2 h.tau_re.2 h.gaps.1 h.gaps.2.1 hgammaHigh hgammaLow
  have h5 := pair_cost chi eta h.chi_dvd h.eta_dvd h.level_le hs.1 hs.2 h.heights.1 h.heights.2.2
    h.rho_re.2 h.upsilon_re.2 h.gaps.1 h.gaps.2.2 hgammaHigh hgammaLow
  have h6 := pair_cost psi eta h.psi_dvd h.eta_dvd h.level_le hs.1 hs.2 h.heights.2.1 h.heights.2.2
    h.tau_re.2 h.upsilon_re.2 h.gaps.2.1 h.gaps.2.2 hgammaHigh hgammaLow
  have h7 := lwd_2_26 (Nat.lcm_dvd (Nat.lcm_dvd h.chi_dvd h.psi_dvd) h.eta_dvd) h.level_le
    (lwdProduct (lwdProduct chi psi) eta) htriple h.heights.1 h.heights.2.1 h.heights.2.2
    hs.1 (by linarith [hs.2])
  unfold nonprincipalCost at h1 h2 h3 h4 h5 h6
  rw [Real.log_mul (by norm_num) hx.ne'] at h4 h5 h6
  unfold lwdG pairCount
  by_cases hp : lwdProduct chi psi = 1 <;>
    by_cases he : lwdProduct chi eta = 1 <;>
    by_cases ht : lwdProduct psi eta = 1 <;>
    simp only [hp, he, ht, if_true, if_false, Nat.cast_add, Nat.cast_zero,
      Nat.cast_one] at h1 h2 h3 h4 h5 h6 h7 ⊢ <;>
    nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]

theorem lwd_case_v {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon) (hn : pairCount chi psi eta = 1)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4396 := by
  have hh := pair_cases_account h (positive_pairCount_triple_nonprincipal h (by omega)) hgammaHigh hgammaLow
  rw [hn] at hh
  norm_num only [Nat.cast_one] at hh
  linarith only [hh, original_product_constants.1]

theorem lwd_case_vi {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon) (hn : pairCount chi psi eta = 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.3795 := by
  have hh := pair_cases_account h (positive_pairCount_triple_nonprincipal h (by omega)) hgammaHigh hgammaLow
  rw [hn] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh, original_product_constants.2.1]

theorem lwd_case_vii {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {rho tau upsilon : ℂ}
    (h : TripleData x q chi psi eta rho tau upsilon) (hn : pairCount chi psi eta = 3)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.3193 := by
  have hh := pair_cases_account h (positive_pairCount_triple_nonprincipal h (by omega)) hgammaHigh hgammaLow
  rw [hn] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh, original_product_constants.2.2]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
