import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.CloseHeight

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

theorem lwd_case_ii_far_constant :
    -0.8973 + 3 * 0.3316 + 4 * 0.3918 +
      stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) ≤ 0.3284 := by
  have hlog : 3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi ≤
      3 * 0.693147181 + 1.098612289 - 7 * 1.144729 := by
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, lwd_log_pi]
  have hh := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  have hk := mul_le_mul_of_nonpos_right lwd_kappa_bounds.1
    (by norm_num : 3 * (0.693147181 : ℝ) + 1.098612289 - 7 * 1.144729 ≤ 0)
  linarith

theorem lwd_case_ii_far_logs {q : ℕ} [NeZero q] {x t u : ℝ}
    (hq : (q : ℝ) ≤ x) (ht : |t| ≤ x / q) (hu : |u| ≤ x / q)
    (ht0 : 0 < |t|) (hu0 : 0 < |u|) (hfar : 1 ≤ |t + u|) :
    Real.log |t| + Real.log |u| + Real.log x + Real.log |t + u| +
      2 * Real.log (2 * x) + Real.log (3 * x) ≤
      7 * Real.log x + 3 * Real.log 2 + Real.log 3 := by
  have hh := lwd_2_23_logs hq ht hu ht0 hu0
  have hp := (paired_height_logs hq ht hu).1
  rw [max_eq_right hfar] at hp
  have hq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  linarith

theorem lwd_case_ii_far {d q : ℕ} [NeZero d] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {rho tau upsilon : ℂ}
    (h : CaseIIData x q chi rho tau upsilon) (hfar : 1 ≤ |rho.im + tau.im|)
    (hgamma1 : gammaHalfDifference (lwdSourceSigma x) rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316)
    (hgamma2 : gammaHalfDifference (lwdSourceSigma x) tau.im ≤
      stechkinConductorCoeff * Real.log |tau.im| + 0.3316)
    (hgamma12 : gammaHalfDifference (lwdSourceSigma x) (rho.im + tau.im) ≤
      stechkinConductorCoeff * Real.log |rho.im + tau.im| + 0.3316) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi
      (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 0.3284 := by
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  rw [principal_damped_eq] at h0
  have h1 := zeta_high_single hs.1 hs1 h.rho_re.1 h.rho_re.2
    h.rho_zero h.zeta_heights.1 hgamma1
  have h2 := zeta_high_single hs.1 hs1 h.tau_re.1 h.tau_re.2
    h.tau_zero h.zeta_heights.2 hgamma2
  have h3 := lwd_2_24 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.upsilon_re.1 h.upsilon_re.2 h.upsilon_zero h.heights.2.2 hs.1 hs1
  have h4 := zeta_high_unselected hs.1 hs1 hfar hgamma12
  have h5 := lwd_2_20 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.heights.1 h.heights.2.2 hs.1 hs1
  have h6 := lwd_2_20 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.heights.2.1 h.heights.2.2 hs.1 hs1
  have h7 := lwd_2_19 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.heights.1 h.heights.2.1 h.heights.2.2 hs.1 hs1
  have hl := lwd_case_ii_far_logs h.level_le h.heights.1 h.heights.2.1
    (by linarith [h.zeta_heights.1]) (by linarith [h.zeta_heights.2]) hfar
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  rw [lwd_case_ii_g chi hs.1]
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, hm, lwd_case_ii_far_constant]

theorem lwd_case_ii {d q : ℕ} [NeZero d] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {rho tau upsilon : ℂ}
    (h : CaseIIData x q chi rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t ≤
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t ≤ 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi
      (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 0.3284 := by
  have h1 := hgammaHigh rho.im (by linarith [h.zeta_heights.1])
  have h2 := hgammaHigh tau.im (by linarith [h.zeta_heights.2])
  by_cases hclose : |rho.im + tau.im| < 1
  · have hh := lwd_2_23_close h hclose h1 h2 (hgammaLow _ hclose)
    linarith only [hh]
  · exact lwd_case_ii_far h (le_of_not_gt hclose) h1 h2
      (hgammaHigh _ (le_of_not_gt hclose))

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
