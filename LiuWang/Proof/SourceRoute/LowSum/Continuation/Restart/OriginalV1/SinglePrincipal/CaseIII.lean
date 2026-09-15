import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal.Selection

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

structure CaseIIIData {d e : ℕ} [NeZero d] [NeZero e] (x : ℝ) (q : ℕ)
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (rho tau upsilon : ℂ) : Prop where
  scale_ge : 8000000000 ≤ x
  level_le : (q : ℝ) ≤ x
  chi_dvd : d ∣ q
  psi_dvd : e ∣ q
  chi_nonprincipal : chi ≠ 1
  psi_nonprincipal : psi ≠ 1
  chi_primitive : chi.IsPrimitive
  psi_primitive : psi.IsPrimitive
  rho_re : 1 / 2 < rho.re ∧ rho.re < 1
  tau_re : 1 / 2 < tau.re ∧ tau.re < 1
  upsilon_re : 1 / 2 < upsilon.re ∧ upsilon.re < 1
  rho_zero : riemannZeta rho = 0
  tau_zero : chi.LFunction tau = 0
  upsilon_zero : psi.LFunction upsilon = 0
  separation : rho ≠ tau ∧ rho ≠ conj tau ∧
    rho ≠ upsilon ∧ rho ≠ conj upsilon ∧ tau ≠ upsilon ∧ tau ≠ conj upsilon
  gaps : 1 - rho.re ≤ lwdSourceSigma x - 1 ∧
    1 - tau.re ≤ lwdSourceSigma x - 1 ∧ 1 - upsilon.re ≤ lwdSourceSigma x - 1
  heights : |rho.im| ≤ x / q ∧ |tau.im| ≤ x / q ∧ |upsilon.im| ≤ x / q
  zeta_height : 1894438 ≤ |rho.im|

theorem case_iii_zeta_selected {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon)
    (hg : gammaHalfDifference (lwdSourceSigma x) rho.im <
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316) :
    zetaDamped (lwdSourceSigma x) rho.im ≤ principalCost x -
      stechkinConductorCoeff * Real.log q - 1 / (lwdSourceSigma x - rho.re) := by
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hh := zeta_high_single hs.1 (by linarith [hs.2]) h.rho_re.1 h.rho_re.2
    h.rho_zero h.zeta_height hg.le
  have hl := conductor_height_log_max_le h.level_le h.heights.1
  rw [max_eq_right (show 1 ≤ |rho.im| by linarith [h.zeta_height])] at hl
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  unfold principalCost
  nlinarith only [hh, hm]

theorem case_iii_level_two {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon) : 2 ≤ q := by
  have hd : d ≠ 1 := by
    intro he
    subst d
    exact h.chi_nonprincipal (Subsingleton.elim _ _)
  have hle := Nat.le_of_dvd (NeZero.pos q) h.chi_dvd
  have hz := NeZero.pos d
  omega

theorem lwd_case_iii_nonprincipal {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon)
    (hmul : lwdProduct chi psi ≠ 1)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    lwdG (1 : DirichletCharacter ℂ 1) chi psi (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  have hx : 0 < x := by linarith [h.scale_ge]
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  rw [principal_damped_eq] at h0
  have h1 := case_iii_zeta_selected h (hgammaHigh _ (by linarith [h.zeta_height]))
  have hq2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num)
    (by exact_mod_cast case_iii_level_two h)
  have hqcredit := mul_le_mul_of_nonneg_left hq2 conductorCoeff_bounds.1
  have h2 := lwd_2_24 h.chi_dvd h.level_le chi h.chi_nonprincipal h.chi_primitive
    h.tau_re.1 h.tau_re.2 h.tau_zero h.heights.2.1 hs.1 hs1
  have h3 := lwd_2_24 h.psi_dvd h.level_le psi h.psi_nonprincipal h.psi_primitive
    h.upsilon_re.1 h.upsilon_re.2 h.upsilon_zero h.heights.2.2 hs.1 hs1
  have h4 := lwd_2_20 h.chi_dvd h.level_le chi h.chi_nonprincipal h.chi_primitive
    h.heights.1 h.heights.2.1 hs.1 hs1
  have h5 := lwd_2_20 h.psi_dvd h.level_le psi h.psi_nonprincipal h.psi_primitive
    h.heights.1 h.heights.2.2 hs.1 hs1
  have h6 := lwd_2_25 (Nat.lcm_dvd h.chi_dvd h.psi_dvd) h.level_le (lwdProduct chi psi)
    hmul h.heights.2.1 h.heights.2.2 hs.1 hs1
  have h7 := lwd_2_26 (Nat.lcm_dvd h.chi_dvd h.psi_dvd) h.level_le (lwdProduct chi psi)
    hmul h.heights.1 h.heights.2.1 h.heights.2.2 hs.1 hs1
  have hbudget := case_iii_nonprincipal_costs hx
  unfold nonprincipalCost principalCost at hbudget h1
  rw [Real.log_mul (by norm_num) hx.ne', Real.log_mul (by norm_num) hx.ne'] at hbudget
  rw [Real.log_mul (by norm_num) hx.ne'] at h4 h5
  rw [case_iii_g chi psi hs.1]
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, hbudget, hqcredit]

theorem lwd_case_iii_principal {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon)
    (hmul : lwdProduct chi psi = 1)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) chi psi (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  have hx : 0 < x := by linarith [h.scale_ge]
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have hz := principal_product_conjugate_zeros chi psi h.chi_nonprincipal h.psi_nonprincipal
    h.chi_primitive h.psi_primitive hmul h.tau_zero h.upsilon_zero
  have hnc : upsilon ≠ conj tau := by
    intro he
    apply h.separation.2.2.2.2.2
    simpa using (congrArg conj he).symm
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  rw [principal_damped_eq] at h0
  have h1 := case_iii_zeta_selected h (hgammaHigh _ (by linarith [h.zeta_height]))
  have hq0 := mul_nonneg conductorCoeff_bounds.1 (Real.log_natCast_nonneg q)
  have h2 := primitive_single_near chi h.chi_nonprincipal h.chi_primitive h.chi_dvd h.level_le
    hs.1 hs1 h.tau_re (by simpa using h.upsilon_re) h.tau_zero hz.1
    h.separation.2.2.2.2.2 h.heights.2.1
  have h3 := primitive_single_near psi h.psi_nonprincipal h.psi_primitive h.psi_dvd h.level_le
    hs.1 hs1 h.upsilon_re (by simpa using h.tau_re) h.upsilon_zero hz.2 hnc h.heights.2.2
  have hy12 : |rho.im + tau.im| ≤ (2 * x) / q := by
    rw [mul_div_assoc]
    linarith [abs_add_le rho.im tau.im, h.heights.1, h.heights.2.1]
  have hy13 : |rho.im + upsilon.im| ≤ (2 * x) / q := by
    rw [mul_div_assoc]
    linarith [abs_add_le rho.im upsilon.im, h.heights.1, h.heights.2.2]
  have hy23 : |tau.im + upsilon.im| ≤ (2 * x) / q := by
    rw [mul_div_assoc]
    linarith [abs_add_le tau.im upsilon.im, h.heights.2.1, h.heights.2.2]
  have hy123 : |rho.im + tau.im + upsilon.im| ≤ (3 * x) / q := by
    rw [mul_div_assoc] at hy12 ⊢
    linarith [abs_add_le (rho.im + tau.im) upsilon.im, h.heights.2.2]
  have hq2 : (q : ℝ) ≤ 2 * x := by linarith [h.level_le]
  have hq3 : (q : ℝ) ≤ 3 * x := by linarith [h.level_le]
  have h4 := primitive_off_near chi h.chi_nonprincipal h.chi_primitive h.chi_dvd hq2 hs.1 hs1
    (by simpa using h.upsilon_re) hz.1 hy12
  have h5 := primitive_off_near psi h.psi_nonprincipal h.psi_primitive h.psi_dvd hq2 hs.1 hs1
    (by simpa using h.tau_re) hz.2 hy13
  simp only [conj_re, conj_im, sub_neg_eq_add] at h2 h3 h4 h5
  rw [add_comm upsilon.im tau.im] at h3
  rw [add_right_comm rho.im upsilon.im tau.im] at h5
  have hlog := rs_log_gap h.zeta_height h.heights.1
  have hlog2 : Real.log q + 6 ≤ Real.log (2 * x) :=
    hlog.trans (Real.log_le_log hx (by linarith))
  have hlog3 : Real.log q + 6 ≤ Real.log (3 * x) :=
    hlog.trans (Real.log_le_log hx (by linarith))
  have h6 := principal_corrected_pair (Nat.lcm_dvd h.chi_dvd h.psi_dvd) hs.1 hs1 hq2 hlog2 hy23
    h.tau_re.2 h.upsilon_re.2 h.gaps.2.1 h.gaps.2.2 hgammaHigh hgammaLow
  have h7 := principal_corrected_pair (Nat.lcm_dvd h.chi_dvd h.psi_dvd) hs.1 hs1 hq3 hlog3 hy123
    h.tau_re.2 h.upsilon_re.2 h.gaps.2.1 h.gaps.2.2 hgammaHigh hgammaLow
  rw [case_iii_g chi psi hs.1, hmul]
  nlinarith only [h0, h1, hq0, h2, h3, h4, h5, h6, h7, case_iii_costs hx]

theorem lwd_case_iii {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) chi psi (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  by_cases hm : lwdProduct chi psi = 1
  · exact lwd_case_iii_principal h hm hgammaHigh hgammaLow
  · exact lwd_case_iii_nonprincipal h hm hgammaHigh

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
