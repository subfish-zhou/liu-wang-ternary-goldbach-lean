import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.ZetaSelection
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.CharacterProducts

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

structure CaseIIData {d : ℕ} [NeZero d] (x : ℝ) (q : ℕ)
    (chi : DirichletCharacter ℂ d) (rho tau upsilon : ℂ) : Prop where
  scale_ge : 8000000000 ≤ x
  level_le : (q : ℝ) ≤ x
  modulus_dvd : d ∣ q
  nonprincipal : chi ≠ 1
  primitive : chi.IsPrimitive
  rho_re : 1 / 2 < rho.re ∧ rho.re < 1
  tau_re : 1 / 2 < tau.re ∧ tau.re < 1
  upsilon_re : 1 / 2 < upsilon.re ∧ upsilon.re < 1
  rho_zero : riemannZeta rho = 0
  tau_zero : riemannZeta tau = 0
  upsilon_zero : chi.LFunction upsilon = 0
  separation : rho ≠ tau ∧ rho ≠ conj tau ∧
    rho ≠ upsilon ∧ rho ≠ conj upsilon ∧ tau ≠ upsilon ∧ tau ≠ conj upsilon
  gaps : 1 - rho.re ≤ lwdSourceSigma x - 1 ∧
    1 - tau.re ≤ lwdSourceSigma x - 1 ∧ 1 - upsilon.re ≤ lwdSourceSigma x - 1
  heights : |rho.im| ≤ x / q ∧ |tau.im| ≤ x / q ∧ |upsilon.im| ≤ x / q
  zeta_heights : 1894438 ≤ |rho.im| ∧ 1894438 ≤ |tau.im|

theorem lwd_2_23_unsimplified {d q : ℕ} [NeZero d] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {rho tau upsilon : ℂ}
    (h : CaseIIData x q chi rho tau upsilon) (hclose : |rho.im + tau.im| < 1)
    (hgamma1 : gammaHalfDifference (lwdSourceSigma x) rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316)
    (hgamma2 : gammaHalfDifference (lwdSourceSigma x) tau.im ≤
      stechkinConductorCoeff * Real.log |tau.im| + 0.3316)
    (hgamma12 : gammaHalfDifference (lwdSourceSigma x) (rho.im + tau.im) ≤ 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi
      (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
      ((1 / ((lwdSourceSigma x : ℂ) - 1 + I * ((rho.im + tau.im : ℝ) : ℂ))).re -
        (1 / ((lwdSourceSigma x : ℂ) - rho.re + I * ((rho.im + tau.im : ℝ) : ℂ))).re -
        (1 / ((lwdSourceSigma x : ℂ) - tau.re + I * ((rho.im + tau.im : ℝ) : ℂ))).re) +
      stechkinConductorCoeff * (Real.log |rho.im| + Real.log |tau.im| + Real.log x +
        2 * Real.log (2 * x) + Real.log (3 * x)) +
      (-0.8973 - 7 * stechkinConductorCoeff * Real.log Real.pi + 0.3316 * 2 +
        (5 + Real.sqrt 5) / 10 * 2 + 0.3918 * 4 + 0.0615) := by
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  rw [principal_damped_eq] at h0
  have h1 := lwd_2_17 hs.1 hs1 h.rho_re.1 h.rho_re.2 h.tau_re.1 h.tau_re.2
    h.rho_zero h.tau_zero h.separation.2.1 hclose h.zeta_heights.1 hgamma1
  have hnc : tau ≠ conj rho := by
    intro he
    apply h.separation.2.1
    simpa using (congrArg conj he).symm
  have h2 := lwd_2_17 hs.1 hs1 h.tau_re.1 h.tau_re.2 h.rho_re.1 h.rho_re.2
    h.tau_zero h.rho_zero hnc (by simpa only [add_comm] using hclose) h.zeta_heights.2 hgamma2
  have h3 := lwd_2_24 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.upsilon_re.1 h.upsilon_re.2 h.upsilon_zero h.heights.2.2 hs.1 hs1
  have h4 := lwd_2_21 hs.1 hgamma12
  have h5 := lwd_2_20 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.heights.1 h.heights.2.2 hs.1 hs1
  have h6 := lwd_2_20 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.heights.2.1 h.heights.2.2 hs.1 hs1
  have h7 := lwd_2_19 h.modulus_dvd h.level_le chi h.nonprincipal h.primitive
    h.heights.1 h.heights.2.1 h.heights.2.2 hs.1 hs1
  rw [lwd_case_ii_g chi hs.1]
  simp only [Complex.ofReal_add] at h4 ⊢
  rw [add_comm (tau.im : ℂ) (rho.im : ℂ)] at h2
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]

theorem lwd_2_23_close_with_logs {d q : ℕ} [NeZero d] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {rho tau upsilon : ℂ}
    (h : CaseIIData x q chi rho tau upsilon) (hclose : |rho.im + tau.im| < 1)
    (hgamma1 : gammaHalfDifference (lwdSourceSigma x) rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316)
    (hgamma2 : gammaHalfDifference (lwdSourceSigma x) tau.im ≤
      stechkinConductorCoeff * Real.log |tau.im| + 0.3316)
    (hgamma12 : gammaHalfDifference (lwdSourceSigma x) (rho.im + tau.im) ≤ 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi
      (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        6 * stechkinConductorCoeff * Real.log x +
        (2 * Real.log 2 + Real.log 3) * stechkinConductorCoeff + 0.6271 := by
  have hh := lwd_2_23_unsimplified h hclose hgamma1 hgamma2 hgamma12
  have hp := lwd_2_23_pole_bracket (u := rho.im + tau.im)
    (lwd_source_parameters h.scale_ge).2.2.1 h.rho_re.2 h.tau_re.2 h.gaps.1 h.gaps.2.1
  have hl := lwd_2_23_logs h.level_le h.heights.1 h.heights.2.1
    (by linarith [h.zeta_heights.1]) (by linarith [h.zeta_heights.2])
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  nlinarith only [hh, hp, hm, lwd_2_23_constant]

theorem lwd_2_23_close {d q : ℕ} [NeZero d] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {rho tau upsilon : ℂ}
    (h : CaseIIData x q chi rho tau upsilon) (hclose : |rho.im + tau.im| < 1)
    (hgamma1 : gammaHalfDifference (lwdSourceSigma x) rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316)
    (hgamma2 : gammaHalfDifference (lwdSourceSigma x) tau.im ≤
      stechkinConductorCoeff * Real.log |tau.im| + 0.3316)
    (hgamma12 : gammaHalfDifference (lwdSourceSigma x) (rho.im + tau.im) ≤ 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi
      (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x := by
  have hh := lwd_2_23_close_with_logs h hclose hgamma1 hgamma2 hgamma12
  nlinarith only [hh, lwd_2_23_absorb h.scale_ge]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
