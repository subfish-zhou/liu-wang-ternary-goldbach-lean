import LiuWang.Proof.PrincipalPsi.Quantitative.HeightSelection
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.GammaBounds
import LiuWang.Proof.PrincipalPsi.ZetaIntegrand

/-! # zeta 的真实保抵消对数导数及分离水平线估计 -/

set_option autoImplicit false
noncomputable section

open Complex Filter Topology
open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.PrincipalPsi.Quantitative

theorem xiFactor_eq (s : ℂ) :
    xiFactor s = Kadiri.zetaPiFactor s * Kadiri.zetaGammaFactor s := by
  rw [xiFactor, Robin1984.zetaPiFactor_eq_cpow_ascii, Kadiri.zetaGammaFactor]
  rw [show -(s / 2) = -s / 2 by ring]

theorem logDeriv_xiFactor {s : ℂ} (hs : -2 < s.re) :
    logDeriv xiFactor s =
      -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  have hg : ∀ n : ℕ, s / 2 + 1 ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    have hnn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hp : Kadiri.zetaPiFactor s ≠ 0 := by simp [Kadiri.zetaPiFactor]
  have hgn : Kadiri.zetaGammaFactor s ≠ 0 := Gamma_ne_zero hg
  rw [show xiFactor = fun z => Kadiri.zetaPiFactor z * Kadiri.zetaGammaFactor z from funext xiFactor_eq,
    logDeriv_mul s hp hgn
      (by unfold Kadiri.zetaPiFactor; fun_prop)
      ((differentiableAt_Gamma _ hg).comp s ((differentiableAt_id.div_const 2).add_const 1)),
    Kadiri.logDeriv_zetaPiFactor, Kadiri.logDeriv_zetaGammaFactor _ hg]
  ring

theorem logDeriv_xi_eq_zeta {s : ℂ} (hs : -2 < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = logDeriv riemannZeta s + 1 / (s - 1) -
      (Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  have hr : regularizedPrincipal 1 s ≠ 0 := by
    rw [regularizedPrincipal_eq hs1, DirichletCharacter.LFunction_modOne_eq]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hz
  have he := xi_eq_factor_regularized_nhds hs
  have hlog : logDeriv riemannXi s =
      logDeriv (fun z => xiFactor z * regularizedPrincipal 1 z) s := by
    rw [logDeriv_apply, logDeriv_apply, he.deriv_eq, he.self_of_nhds]
  have heR : regularizedPrincipal 1 =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz1
    rw [regularizedPrincipal_eq hz1, DirichletCharacter.LFunction_modOne_eq]
  have hrlog : logDeriv (regularizedPrincipal 1) s =
      logDeriv (fun z : ℂ => (z - 1) * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, heR.deriv_eq, heR.self_of_nhds]
  rw [hlog, logDeriv_mul s (xiFactor_ne_zero hs) hr
      (analytic_xiFactor hs).differentiableAt (analytic_regularizedPrincipal 1 s).differentiableAt,
    logDeriv_xiFactor hs, hrlog,
    logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta)
      s (sub_ne_zero.mpr hs1) hz (by fun_prop)
      (differentiableAt_riemannZeta hs1)]
  simp only [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  ring

theorem xi_hadamard_logDeriv {s : ℂ}
    (hs : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p) :
    logDeriv riemannXi s = logDeriv riemannXi 0 + ∑' p, xiTerm s p := by
  obtain ⟨P, hP⟩ := riemannXi_hadamard_factorization_no_monomial
  rw [logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hP.2 hs,
    Robin1984.riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero hP.1 hP.2]
  rfl

theorem xi_reciprocal_difference_summable {s : ℂ}
    (hs : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p) (H : ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      1 / (s - riemannXiDivisorZeroValue p) -
        1 / (referencePoint H - riemannXiDivisorZeroValue p)) := by
  have ha := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hs
  have hb := xiTerm_summable (s := referencePoint H) (by norm_num [referencePoint])
  exact (ha.sub hb).congr (fun p => by dsimp [xiTerm]; ring)

theorem zeta_logDeriv_difference {s : ℂ} (hs : -2 < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0)
    (haway : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p) (H : ℝ) :
    logDeriv riemannZeta s =
      logDeriv riemannZeta (referencePoint H) +
      (1 / (referencePoint H - 1) - 1 / (s - 1)) +
      (1 / 2 : ℂ) * (digamma (referencePoint H / 2 + 1) - digamma (s / 2 + 1)) +
      ∑' p : RiemannXiDivisorZeroIndex,
        (1 / (s - riemannXiDivisorZeroValue p) -
          1 / (referencePoint H - riemannXiDivisorZeroValue p)) := by
  have hwre : 1 < (referencePoint H).re := by norm_num [referencePoint]
  have hwaway : ∀ p : RiemannXiDivisorZeroIndex,
      referencePoint H ≠ riemannXiDivisorZeroValue p := by
    intro p hp
    have h := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    rw [← hp] at h
    linarith
  have hws1 : referencePoint H ≠ 1 := by intro h; simp [h] at hwre
  have h1 := logDeriv_xi_eq_zeta hs hs1 hz
  have h2 := logDeriv_xi_eq_zeta (s := referencePoint H) (by linarith)
    hws1 (riemannZeta_ne_zero_of_one_lt_re hwre)
  rw [xi_hadamard_logDeriv haway] at h1
  rw [xi_hadamard_logDeriv hwaway] at h2
  have hsum :
      (∑' p : RiemannXiDivisorZeroIndex,
        (1 / (s - riemannXiDivisorZeroValue p) -
          1 / (referencePoint H - riemannXiDivisorZeroValue p))) =
      (∑' p, xiTerm s p) - ∑' p, xiTerm (referencePoint H) p := by
    have hss : Summable (xiTerm s) := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ haway
    rw [← hss.tsum_sub (xiTerm_summable (s := referencePoint H) (by linarith))]
    apply tsum_congr
    intro p
    dsimp [xiTerm]
    ring
  rw [hsum]
  linear_combination h2 - h1

theorem norm_xi_reciprocal_difference_separated {H B : ℝ} (hB : 0 < B)
    (hsep : ∀ p : RiemannXiDivisorZeroIndex,
      B⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - H|)
    {s : ℂ} (him : s.im = H) (hlo : -1 / 2 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖∑' p : RiemannXiDivisorZeroIndex,
      (1 / (s - riemannXiDivisorZeroValue p) -
        1 / (referencePoint H - riemannXiDivisorZeroValue p))‖ ≤
      (5 / 2 + (5 / 2) ^ 2 * B) * referenceMass H := by
  have haway : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p := by
    intro p hp
    have h := hsep p
    rw [← hp, him, sub_self, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hB)) h
  have hs := xi_reciprocal_difference_summable haway H
  have hmajor := (Complex.reCLM.summable
    (xiTerm_summable (s := referencePoint H) (by norm_num [referencePoint]))).mul_left
      (5 / 2 + (5 / 2) ^ 2 * B)
  calc
    _ ≤ ∑' p : RiemannXiDivisorZeroIndex,
        ‖1 / (s - riemannXiDivisorZeroValue p) -
          1 / (referencePoint H - riemannXiDivisorZeroValue p)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' p, (5 / 2 + (5 / 2) ^ 2 * B) * (xiTerm (referencePoint H) p).re := by
      apply hs.norm.tsum_le_tsum _ hmajor
      intro p
      have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
      have h := HorizontalEstimate.norm_reciprocal_difference_le_reference_kernel
        hB (hsep p) him (d := 5 / 2) (by norm_num) (by linarith) hhi ⟨hr.1.le, hr.2.le⟩
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have hn : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
        rw [one_div, Complex.inv_re]
        exact div_nonneg hr.1.le (Complex.normSq_nonneg _)
      exact le_add_of_nonneg_right hn
    _ = (5 / 2 + (5 / 2) ^ 2 * B) * (∑' p, xiTerm (referencePoint H) p).re := by
      rw [tsum_mul_left, Complex.re_tsum
        (xiTerm_summable (by norm_num [referencePoint]))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (xi_reference_kernel_sum_le H) (by positivity)

theorem zeta_ne_zero_separated {H B : ℝ} (hB : 0 < B)
    (hsep : ∀ p : RiemannXiDivisorZeroIndex,
      B⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - H|)
    {s : ℂ} (him : s.im = H) (hlo : -1 / 2 ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hr := zeta_zero_strip (by linarith) hz
  obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero hr.1 hz
  have h := hsep p
  rw [hp, him, sub_self, abs_zero] at h
  exact (not_le_of_gt (inv_pos.mpr hB)) h

def horizontalLogBound (H B : ℝ) : ℝ :=
  20 + 8 * Real.log (|H| + 2) + (5 / 2 + (5 / 2) ^ 2 * B) * referenceMass H

theorem norm_logDeriv_zeta_separated {H B : ℝ} (hB : 0 < B) (hH : 2 ≤ |H|)
    (hsep : ∀ p : RiemannXiDivisorZeroIndex,
      B⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - H|)
    {s : ℂ} (him : s.im = H) (hlo : -1 / 2 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖logDeriv riemannZeta s‖ ≤ horizontalLogBound H B := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at him; norm_num [← him] at hH
  have haway : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p := by
    intro p hp
    have h := hsep p
    rw [← hp, him, sub_self, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hB)) h
  have hz := zeta_ne_zero_separated hB hsep him hlo
  have hdiff := zeta_logDeriv_difference (by linarith) hs1 hz haway H
  have hbase : ‖logDeriv riemannZeta (referencePoint H)‖ ≤ 6 := by
    have h := norm_neg_logDeriv_LFunction_le_zeta_re
      (1 : DirichletCharacter ℂ 1) (s := referencePoint H) (by norm_num [referencePoint])
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    simpa only [logDeriv_apply, norm_div, norm_neg] using
      h.trans (by simpa [referencePoint] using norm_neg_logDeriv_zeta_two_le_six)
  have hpole : ‖1 / (referencePoint H - 1) - 1 / (s - 1)‖ ≤ 1 := by
    have hn (z : ℂ) (hz : z.im = H) : ‖1 / (z - 1)‖ ≤ 1 / 2 := by
      rw [norm_div, norm_one]
      apply one_div_le_one_div_of_le (by norm_num)
      have h := Complex.abs_im_le_norm (z - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero, hz] at h
      linarith
    exact (norm_sub_le _ _).trans (by
      linarith [hn (referencePoint H) (by simp [referencePoint]), hn s him])
  have hg (z : ℂ) (hzlo : -1 / 2 ≤ z.re) (hzhi : z.re ≤ 2) (hz : z.im = H) :
      ‖digamma (z / 2 + 1)‖ ≤ 8 * Real.log (|H| + 2) + 13 := by
    have h := HorizontalEstimate.norm_digamma_le_explicit (z := z / 2 + 1)
      (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith)
      (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith)
    have hh : |(z / 2 + 1).im| ≤ |H| := by simp [hz, abs_div]
    exact h.trans (by
      have hl := Real.log_le_log (by positivity : 0 < |(z / 2 + 1).im| + 2)
        (by linarith : |(z / 2 + 1).im| + 2 ≤ |H| + 2)
      linarith)
  have hgamma : ‖(1 / 2 : ℂ) *
      (digamma (referencePoint H / 2 + 1) - digamma (s / 2 + 1))‖ ≤
      8 * Real.log (|H| + 2) + 13 := by
    rw [norm_mul]
    norm_num
    have h := norm_sub_le (digamma (referencePoint H / 2 + 1)) (digamma (s / 2 + 1))
    linarith [hg s hlo hhi him, hg (referencePoint H)
      (by norm_num [referencePoint]) (by norm_num [referencePoint]) (by simp [referencePoint])]
  have hzeros := norm_xi_reciprocal_difference_separated hB hsep him hlo hhi
  rw [hdiff]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans
      (by unfold horizontalLogBound; linarith)

end LiuWang.Proof.PrincipalPsi.Quantitative
