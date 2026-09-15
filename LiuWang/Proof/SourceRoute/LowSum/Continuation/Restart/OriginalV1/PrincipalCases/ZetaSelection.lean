import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.Kernels

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

theorem zeta_reflected_pair_le {sigma : ℝ} (hs : 1 < sigma)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1)
    (hzr : riemannZeta rho = 0) (hzt : riemannZeta tau = 0)
    (hne : rho ≠ tau) (t : ℝ) :
    reflectedKernel sigma t rho + reflectedKernel sigma t tau ≤ zetaZeroSum sigma t := by
  have hm := principal_ordinary_mass_le 1 hs t {rho, tau} (by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · simpa only [h] using And.intro hr hr1
    · simpa only [Finset.mem_singleton.mp h] using And.intro ht ht1)
  have hnr : rho ≠ 1 := by intro he; simp [he] at hr1
  have hnt : tau ≠ 1 := by intro he; simp [he] at ht1
  have hir : (1 : ℝ) ≤ analyticOrderNatAt (1 : DirichletCharacter ℂ 1).LFunction rho := by
    exact_mod_cast ordinary_zero_order_pos (1 : DirichletCharacter ℂ 1) hnr
      (by simpa only [DirichletCharacter.LFunction_modOne_eq] using hzr)
  have hit : (1 : ℝ) ≤ analyticOrderNatAt (1 : DirichletCharacter ℂ 1).LFunction tau := by
    exact_mod_cast ordinary_zero_order_pos (1 : DirichletCharacter ℂ 1) hnt
      (by simpa only [DirichletCharacter.LFunction_modOne_eq] using hzt)
  have hkr : 0 ≤ reflectedKernel sigma t rho :=
    dampedZeroKernel_pair_nonneg hs t ⟨by linarith, hr1.le⟩
  have hkt : 0 ≤ reflectedKernel sigma t tau :=
    dampedZeroKernel_pair_nonneg hs t ⟨by linarith, ht1.le⟩
  have h1 := mul_le_mul_of_nonneg_right hir hkr
  have h2 := mul_le_mul_of_nonneg_right hit hkt
  simp only [Finset.sum_pair hne] at hm
  linarith

theorem lwd_2_17_zero_selection {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1)
    (hzr : riemannZeta rho = 0) (hzt : riemannZeta tau = 0)
    (hnc : rho ≠ conj tau) (hclose : |rho.im + tau.im| < 1) :
    1 / (sigma - rho.re) + realKernel (sigma - tau.re) (rho.im + tau.im) -
      (5 + Real.sqrt 5) / 10 ≤ zetaZeroSum sigma rho.im := by
  have hconj : riemannZeta (conj tau) = 0 := by
    rw [riemannZeta_conj, hzt, map_zero]
  have hm := zeta_reflected_pair_le hs hr hr1 (by simpa using ht)
    (by simpa using ht1) hzr hconj hnc rho.im
  have hsame := selected_pair_dominates hs ⟨by linarith, hr1⟩
  have hoff := lwd_2_16_kernel hs hs1 (rho := conj tau) (by simpa using ht.le)
    (by simpa using ht1) (t := rho.im) (by simpa using hclose.le)
  change _ ≤ reflectedKernel sigma rho.im rho at hsame
  simp only [conj_re, conj_im, sub_neg_eq_add] at hoff
  linarith

theorem lwd_2_17 {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1)
    (hzr : riemannZeta rho = 0) (hzt : riemannZeta tau = 0)
    (hnc : rho ≠ conj tau) (hclose : |rho.im + tau.im| < 1)
    (hheight : 1894438 ≤ |rho.im|)
    (hgamma : gammaHalfDifference sigma rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316) :
    zetaDamped sigma rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| - stechkinConductorCoeff * Real.log Real.pi +
        0.3316 - 1 / (sigma - rho.re) -
        (1 / ((sigma : ℂ) - tau.re + I * (rho.im + tau.im))).re +
        (5 + Real.sqrt 5) / 10 := by
  have hsel := lwd_2_17_zero_selection hs hs1 hr hr1 ht ht1 hzr hzt hnc hclose
  have hident := zeta_full_zero_sum_identity hs rho.im
  have hpole := poleDifference_high_nonpos hs (by linarith : sigma ≤ 23 / 20)
    (show 1 ≤ |rho.im| by linarith)
  rw [shiftedGamma_eq] at hident
  rw [realKernel_eq_inverse_re] at hsel
  simp only [Complex.ofReal_sub, Complex.ofReal_add] at hsel
  linarith

theorem lwd_2_21 {sigma t : ℝ} (hs : 1 < sigma)
    (hgamma : gammaHalfDifference sigma t ≤ 0.0615) :
    zetaDamped sigma t ≤ (1 / ((sigma : ℂ) - 1 + I * t)).re -
      stechkinConductorCoeff * Real.log Real.pi + 0.0615 := by
  have hz := zeta_damped_pole_bound hs t
  have hp := poleDifference_le_realKernel hs t
  rw [shiftedGamma_eq] at hz
  rw [realKernel_eq_inverse_re] at hp
  simp only [Complex.ofReal_sub, Complex.ofReal_one] at hp
  linarith

theorem zeta_single_selected {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1) (hz : riemannZeta rho = 0) :
    1 / (sigma - rho.re) ≤ zetaZeroSum sigma rho.im := by
  have hm := lwd_2_16_principal 1 hs hs1 rho.im {rho} ∅ (Finset.disjoint_empty_right _)
    (by
      intro z h
      rw [Finset.mem_singleton.mp h]
      exact ⟨hr, hr1, rfl⟩)
    (by simp)
  have hi : (1 : ℝ) ≤ analyticOrderNatAt (1 : DirichletCharacter ℂ 1).LFunction rho := by
    exact_mod_cast ordinary_zero_order_pos (1 : DirichletCharacter ℂ 1)
      (by intro h; simp [h] at hr1)
      (by simpa only [DirichletCharacter.LFunction_modOne_eq] using hz)
  have hh := div_le_div_of_nonneg_right hi (show 0 ≤ sigma - rho.re by linarith)
  simp only [Finset.sum_singleton, Finset.sum_empty, mul_zero, sub_zero, add_zero] at hm
  linarith

theorem zeta_high_single {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1) (hz : riemannZeta rho = 0)
    (hheight : 1894438 ≤ |rho.im|)
    (hgamma : gammaHalfDifference sigma rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316) :
    zetaDamped sigma rho.im ≤
      stechkinConductorCoeff * Real.log |rho.im| - stechkinConductorCoeff * Real.log Real.pi +
        0.3316 - 1 / (sigma - rho.re) := by
  have hsel := zeta_single_selected hs hs1 hr hr1 hz
  have hident := zeta_full_zero_sum_identity hs rho.im
  have hpole := poleDifference_high_nonpos hs (by linarith : sigma ≤ 23 / 20)
    (show 1 ≤ |rho.im| by linarith)
  rw [shiftedGamma_eq] at hident
  linarith

theorem zeta_high_unselected {sigma t : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    (ht : 1 ≤ |t|)
    (hgamma : gammaHalfDifference sigma t ≤ stechkinConductorCoeff * Real.log |t| + 0.3316) :
    zetaDamped sigma t ≤
      stechkinConductorCoeff * Real.log |t| - stechkinConductorCoeff * Real.log Real.pi + 0.3316 := by
  have hz := zeta_damped_pole_bound hs t
  have hp := poleDifference_high_nonpos hs (by linarith : sigma ≤ 23 / 20) ht
  rw [shiftedGamma_eq] at hz
  linarith

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
