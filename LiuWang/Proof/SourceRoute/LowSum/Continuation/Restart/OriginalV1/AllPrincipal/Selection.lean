import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal.Kernels

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal

theorem zeta_selected_reflections {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) (s : Finset ℂ)
    (hr : ∀ z ∈ s, 1 / 2 < z.re ∧ z.re < 1)
    (hz : ∀ z ∈ s, riemannZeta z = 0) :
    (∑ z ∈ s, reflectedKernel sigma t z) ≤ zetaZeroSum sigma t := by
  have hm := principal_ordinary_mass_le 1 hs t s hr
  apply le_trans _ hm
  apply Finset.sum_le_sum
  intro z h
  have ho : (1 : ℝ) ≤ analyticOrderNatAt (1 : DirichletCharacter ℂ 1).LFunction z := by
    exact_mod_cast ordinary_zero_order_pos (1 : DirichletCharacter ℂ 1)
      (by intro he; simpa [he] using (hr z h).2)
      (by simpa only [DirichletCharacter.LFunction_modOne_eq] using hz z h)
  have hn : 0 ≤ reflectedKernel sigma t z :=
    dampedZeroKernel_pair_nonneg hs t ⟨by linarith [(hr z h).1], (hr z h).2.le⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ho hn

theorem zeta_three_reflections {sigma : ℝ} (hs : 1 < sigma) (t : ℝ)
    {rho tau upsilon : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) (ht : 1 / 2 < tau.re ∧ tau.re < 1)
    (hu : 1 / 2 < upsilon.re ∧ upsilon.re < 1)
    (hzr : riemannZeta rho = 0) (hzt : riemannZeta tau = 0) (hzu : riemannZeta upsilon = 0)
    (hrt : rho ≠ tau) (hru : rho ≠ upsilon) (htu : tau ≠ upsilon) :
    reflectedKernel sigma t rho + reflectedKernel sigma t tau + reflectedKernel sigma t upsilon ≤
      zetaZeroSum sigma t := by
  have hh := zeta_selected_reflections hs t {rho, tau, upsilon}
    (by simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
      And.intro hr (And.intro ht hu))
    (by simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
      And.intro hzr (And.intro hzt hzu))
  simpa [Finset.sum_insert, hrt, hru, htu, add_assoc] using hh

theorem single_with_pair_debits {sigma y : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho tau upsilon : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) (ht : 1 / 2 < tau.re ∧ tau.re < 1)
    (hu : 1 / 2 < upsilon.re ∧ upsilon.re < 1)
    (hzr : riemannZeta rho = 0) (hzt : riemannZeta tau = 0) (hzu : riemannZeta upsilon = 0)
    (hrt : rho ≠ conj tau) (hru : rho ≠ conj upsilon) (htu : tau ≠ upsilon)
    (hheight : 1894438 ≤ |rho.im|) (hy : |rho.im| ≤ y)
    (hgamma : gammaHalfDifference sigma rho.im <
      stechkinConductorCoeff * Real.log |rho.im| + 0.3316) :
    zetaDamped sigma rho.im ≤ principalCost y - 1 / (sigma - rho.re) -
      nearDebit sigma tau.re (rho.im + tau.im) -
      nearDebit sigma upsilon.re (rho.im + upsilon.im) := by
  have hctu : conj tau ≠ conj upsilon := by
    intro he
    apply htu
    simpa using congrArg conj he
  have hm := zeta_three_reflections hs rho.im hr
    (by simpa using ht) (by simpa using hu) hzr
    (by rw [riemannZeta_conj, hzt, map_zero])
    (by rw [riemannZeta_conj, hzu, map_zero]) hrt hru hctu
  have h0 := selected_pair_dominates hs ⟨by linarith [hr.1], hr.2⟩
  change _ ≤ reflectedKernel sigma rho.im rho at h0
  have h1 := nearDebit_le_reflected hs hs1 (rho := conj tau)
    (by simpa using ht.1) (by simpa using ht.2) rho.im
  have h2 := nearDebit_le_reflected hs hs1 (rho := conj upsilon)
    (by simpa using hu.1) (by simpa using hu.2) rho.im
  simp only [conj_re, conj_im, sub_neg_eq_add] at h1 h2
  have hid := zeta_full_zero_sum_identity hs rho.im
  rw [shiftedGamma_eq] at hid
  have hp := poleDifference_high_nonpos hs (by linarith : sigma ≤ 23 / 20)
    (show 1 ≤ |rho.im| by linarith)
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_log (by linarith : 0 < |rho.im|) hy) conductorCoeff_bounds.1
  unfold principalCost
  linarith

theorem high_off_zero {sigma t y : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho : ℂ} (hr : 1 / 2 < rho.re ∧ rho.re < 1) (hz : riemannZeta rho = 0)
    (ht : 1 ≤ |t|) (hy : |t| ≤ y) (hnear : |t - rho.im| < 1)
    (hgamma : gammaHalfDifference sigma t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    zetaDamped sigma t ≤ principalCost y - offDebit sigma rho.re (t - rho.im) := by
  have hm := zeta_selected_reflections hs t {rho}
    (by simpa only [Finset.mem_singleton, forall_eq] using hr)
    (by simpa only [Finset.mem_singleton, forall_eq] using hz)
  simp only [Finset.sum_singleton] at hm
  have hk := lwd_2_16_kernel hs hs1 hr.1.le hr.2 hnear.le
  have hid := zeta_full_zero_sum_identity hs t
  rw [shiftedGamma_eq] at hid
  have hp := poleDifference_high_nonpos hs (by linarith : sigma ≤ 23 / 20) ht
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_log (by linarith : 0 < |t|) hy) conductorCoeff_bounds.1
  unfold principalCost offDebit
  linarith

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal
