import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal.Selection
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.FourPhases

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal

structure CaseIData (x : ℝ) (q : ℕ) (rho tau upsilon : ℂ) : Prop where
  scale_ge : 8000000000 ≤ x
  level_le : (q : ℝ) ≤ x
  rho_re : 1 / 2 < rho.re ∧ rho.re < 1
  tau_re : 1 / 2 < tau.re ∧ tau.re < 1
  upsilon_re : 1 / 2 < upsilon.re ∧ upsilon.re < 1
  rho_zero : riemannZeta rho = 0
  tau_zero : riemannZeta tau = 0
  upsilon_zero : riemannZeta upsilon = 0
  separation : rho ≠ tau ∧ rho ≠ conj tau ∧
    rho ≠ upsilon ∧ rho ≠ conj upsilon ∧ tau ≠ upsilon ∧ tau ≠ conj upsilon
  gaps : 1 - rho.re ≤ lwdSourceSigma x - 1 ∧
    1 - tau.re ≤ lwdSourceSigma x - 1 ∧ 1 - upsilon.re ≤ lwdSourceSigma x - 1
  heights : |rho.im| ≤ x / q ∧ |tau.im| ≤ x / q ∧ |upsilon.im| ≤ x / q
  zeta_heights : 1894438 ≤ |rho.im| ∧ 1894438 ≤ |tau.im| ∧ 1894438 ≤ |upsilon.im|

theorem case_i_g {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
      (1 : DirichletCharacter ℂ 1) sigma t u v =
      zetaDamped sigma 0 + zetaDamped sigma t + zetaDamped sigma u + zetaDamped sigma v +
      zetaDamped sigma (t + u) + zetaDamped sigma (t + v) + zetaDamped sigma (u + v) +
      zetaDamped sigma (t + u + v) := by
  simpa only [principal_damped_eq] using lwd_case_ii_g (1 : DirichletCharacter ℂ 1) hs t u v

theorem case_i_heights {x : ℝ} {q : ℕ} [NeZero q] {rho tau upsilon : ℂ}
    (h : CaseIData x q rho tau upsilon) :
    |rho.im| ≤ x ∧ |tau.im| ≤ x ∧ |upsilon.im| ≤ x := by
  have hh : x / q ≤ x := div_le_self (by linarith [h.scale_ge])
    (by exact_mod_cast NeZero.pos q)
  exact ⟨h.heights.1.trans hh, h.heights.2.1.trans hh, h.heights.2.2.trans hh⟩

theorem three_singles_with_pair_debits {x : ℝ} {q : ℕ} [NeZero q] {rho tau upsilon : ℂ}
    (h : CaseIData x q rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    zetaDamped (lwdSourceSigma x) rho.im + zetaDamped (lwdSourceSigma x) tau.im +
      zetaDamped (lwdSourceSigma x) upsilon.im ≤
      3 * principalCost x -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) -
        nearDebit (lwdSourceSigma x) rho.re (rho.im + tau.im) -
        nearDebit (lwdSourceSigma x) tau.re (rho.im + tau.im) -
        nearDebit (lwdSourceSigma x) rho.re (rho.im + upsilon.im) -
        nearDebit (lwdSourceSigma x) upsilon.re (rho.im + upsilon.im) -
        nearDebit (lwdSourceSigma x) tau.re (tau.im + upsilon.im) -
        nearDebit (lwdSourceSigma x) upsilon.re (tau.im + upsilon.im) := by
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have hh := case_i_heights h
  have htr : tau ≠ conj rho := by
    intro he
    apply h.separation.2.1
    simpa using (congrArg conj he).symm
  have hur : upsilon ≠ conj rho := by
    intro he
    apply h.separation.2.2.2.1
    simpa using (congrArg conj he).symm
  have hut : upsilon ≠ conj tau := by
    intro he
    apply h.separation.2.2.2.2.2
    simpa using (congrArg conj he).symm
  have h1 := single_with_pair_debits hs.1 hs1 h.rho_re h.tau_re h.upsilon_re
    h.rho_zero h.tau_zero h.upsilon_zero h.separation.2.1 h.separation.2.2.2.1
    h.separation.2.2.2.2.1 h.zeta_heights.1 hh.1
    (hgammaHigh _ (by linarith [h.zeta_heights.1]))
  have h2 := single_with_pair_debits hs.1 hs1 h.tau_re h.rho_re h.upsilon_re
    h.tau_zero h.rho_zero h.upsilon_zero htr h.separation.2.2.2.2.2
    h.separation.2.2.1 h.zeta_heights.2.1 hh.2.1
    (hgammaHigh _ (by linarith [h.zeta_heights.2.1]))
  have h3 := single_with_pair_debits hs.1 hs1 h.upsilon_re h.rho_re h.tau_re
    h.upsilon_zero h.rho_zero h.tau_zero hur hut h.separation.1 h.zeta_heights.2.2 hh.2.2
    (hgammaHigh _ (by linarith [h.zeta_heights.2.2]))
  rw [add_comm tau.im rho.im] at h2
  rw [add_comm upsilon.im rho.im, add_comm upsilon.im tau.im] at h3
  linarith only [h1, h2, h3]

theorem lwd_case_i_ledger {x : ℝ} {q : ℕ} [NeZero q] {rho tau upsilon : ℂ}
    (h : CaseIData x q rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
      (1 : DirichletCharacter ℂ 1) (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) -
        0.8973 + 3 * principalCost x + 3 * principalCost (2 * x) + principalCost (3 * x) := by
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have hh := case_i_heights h
  have hy2 : 8000000000 ≤ 2 * x := by linarith [h.scale_ge]
  have hy3 : 8000000000 ≤ 3 * x := by linarith [h.scale_ge]
  have hb12 : |rho.im + tau.im| ≤ 2 * x := by linarith [abs_add_le rho.im tau.im, hh.1, hh.2.1]
  have hb13 : |rho.im + upsilon.im| ≤ 2 * x := by
    linarith [abs_add_le rho.im upsilon.im, hh.1, hh.2.2]
  have hb23 : |tau.im + upsilon.im| ≤ 2 * x := by
    linarith [abs_add_le tau.im upsilon.im, hh.2.1, hh.2.2]
  have hb123 : |rho.im + tau.im + upsilon.im| ≤ 3 * x := by
    linarith [abs_add_le (rho.im + tau.im) upsilon.im, hh.2.2]
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  rw [principal_damped_eq] at h0
  have hS := three_singles_with_pair_debits h hgammaHigh
  rw [case_i_g hs.1]
  by_cases hc : |rho.im + tau.im + upsilon.im| < 1
  · have ht12 := triple_close_pair_high (t := rho.im) (u := tau.im)
      (by linarith [h.zeta_heights.2.2] : 2 ≤ |upsilon.im|) hc
    have ht13 := triple_close_pair_high (t := rho.im) (u := upsilon.im)
      (by linarith [h.zeta_heights.2.1] : 2 ≤ |tau.im|)
      (by simpa only [add_right_comm] using hc)
    have ht23 := triple_close_pair_high (t := tau.im) (u := upsilon.im)
      (by linarith [h.zeta_heights.1] : 2 ≤ |rho.im|)
      (by rwa [show tau.im + upsilon.im + rho.im = rho.im + tau.im + upsilon.im by ring])
    simp only [nearDebit, if_neg (not_lt.mpr ht12), if_neg (not_lt.mpr ht13),
      if_neg (not_lt.mpr ht23), sub_zero] at hS
    have h12 := high_off_zero hs.1 hs1 (rho := conj upsilon)
      (by simpa using h.upsilon_re) (by rw [riemannZeta_conj, h.upsilon_zero, map_zero])
      ht12 hb12 (by simpa only [conj_im, sub_neg_eq_add] using hc)
      (hgammaHigh _ ht12)
    have h13 := high_off_zero hs.1 hs1 (rho := conj tau)
      (by simpa using h.tau_re) (by rw [riemannZeta_conj, h.tau_zero, map_zero])
      ht13 hb13 (by simpa only [conj_im, sub_neg_eq_add, add_right_comm] using hc)
      (hgammaHigh _ ht13)
    simp only [conj_re, conj_im, sub_neg_eq_add] at h12 h13
    rw [add_right_comm rho.im upsilon.im tau.im] at h13
    have h23 := high_cost hs.1 hs1 ht23 hb23 (hgammaHigh _ ht23)
    have h123 := low_two_debits hs.1 hy3 h.upsilon_re.2 h.tau_re.2
      h.gaps.2.2 h.gaps.2.1 (hgammaLow _ hc)
    linarith only [h0, hS, h12, h13, h23, h123]
  · have h12 := pair_cost hs.1 hs1 hy2 hb12 h.rho_re.2 h.tau_re.2
      h.gaps.1 h.gaps.2.1 hgammaHigh hgammaLow
    have h13 := pair_cost hs.1 hs1 hy2 hb13 h.rho_re.2 h.upsilon_re.2
      h.gaps.1 h.gaps.2.2 hgammaHigh hgammaLow
    have h23 := pair_cost hs.1 hs1 hy2 hb23 h.tau_re.2 h.upsilon_re.2
      h.gaps.2.1 h.gaps.2.2 hgammaHigh hgammaLow
    have h123 := high_cost hs.1 hs1 (le_of_not_gt hc) hb123 (hgammaHigh _ (le_of_not_gt hc))
    linarith only [h0, hS, h12, h13, h23, h123]

theorem lwd_case_i {x : ℝ} {q : ℕ} [NeZero q] {rho tau upsilon : ℂ}
    (h : CaseIData x q rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
      (1 : DirichletCharacter ℂ 1) (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 0.0876 := by
  have hh := lwd_case_i_ledger h hgammaHigh hgammaLow
  linarith only [hh, seven_costs (show 0 < x by linarith [h.scale_ge])]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal
