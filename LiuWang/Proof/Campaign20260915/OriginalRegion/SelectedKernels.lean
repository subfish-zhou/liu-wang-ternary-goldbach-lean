import LiuWang.Proof.Campaign20260915.OriginalRegion.SignedCosts
import LiuWang.Proof.ZeroRegionFamily.RealClosure.QuarticPositivity
import LiuWang.Proof.NearOneDensity.Multiplicity

/-! Exact reflected kernels and their signed harmonic budget, with no real seed. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem reflectedKernel_eq_rational (sigma t : ℝ) (rho : ℂ) :
    reflectedKernel sigma t rho =
      (sigma - rho.re) / ((sigma - rho.re) ^ 2 + (t - rho.im) ^ 2) +
      (sigma - 1 + rho.re) / ((sigma - 1 + rho.re) ^ 2 + (t - rho.im) ^ 2) -
      stechkinK *
        ((stechkinSigma sigma - rho.re) /
          ((stechkinSigma sigma - rho.re) ^ 2 + (t - rho.im) ^ 2) +
        (stechkinSigma sigma - 1 + rho.re) /
          ((stechkinSigma sigma - 1 + rho.re) ^ 2 + (t - rho.im) ^ 2)) := by
  simp [reflectedKernel, dampedZeroKernel, one_div, Complex.inv_re,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem reflectedKernel_centered_eq {sigma : ℝ} (hs : 1 < sigma)
    {rho : ℂ} (hr : rho.re ∈ Set.Ioo (0 : ℝ) 1) :
    reflectedKernel sigma rho.im rho =
      1 / (sigma - rho.re) + 1 / (sigma - 1 + rho.re) -
        stechkinK * (1 / (stechkinSigma sigma - rho.re) +
          1 / (stechkinSigma sigma - 1 + rho.re)) := by
  have hge := stechkinSigma_ge hs
  have h0 : sigma - rho.re ≠ 0 := by linarith [hr.2]
  have h1 : sigma - 1 + rho.re ≠ 0 := by linarith [hr.1]
  have h2 : stechkinSigma sigma - rho.re ≠ 0 := by linarith [hr.2]
  have h3 : stechkinSigma sigma - 1 + rho.re ≠ 0 := by linarith [hr.1]
  rw [reflectedKernel_eq_rational]
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  field_simp

theorem centered_surplus_nonneg {sigma : ℝ} (hs : 1 < sigma)
    {rho : ℂ} (hr : rho.re ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ reflectedKernel sigma rho.im rho - 1 / (sigma - rho.re) := by
  exact sub_nonneg.mpr (selected_pair_dominates hs hr)

theorem reflectedKernel_le_singleton_mass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) {rho : ℂ} (hr : rho.re ∈ Set.Ioo (0 : ℝ) 1)
    (hz : chi.LFunction rho = 0) :
    reflectedKernel sigma t rho ≤ ordinaryMass chi sigma t {rho} := by
  have hm := NearOneDensity.ordinary_zero_multiplicity_pos chi
    (by intro hh; have h := hr.2; rw [hh] at h; norm_num at h) hz
  have hk : 0 ≤ reflectedKernel sigma t rho :=
    dampedZeroKernel_pair_nonneg hs t ⟨hr.1.le, hr.2.le⟩
  have hmul := mul_le_mul_of_nonneg_right
    (show (1 : ℝ) ≤ analyticOrderNatAt chi.LFunction rho by exact_mod_cast hm) hk
  simpa only [ordinaryMass, Finset.sum_singleton, one_mul] using hmul

theorem signed_singleton_selected_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) {rho : ℂ} (hr : 1 / 2 < rho.re ∧ rho.re < 1)
    (hz : chi.LFunction rho = 0) :
    f chi sigma t + reflectedKernel sigma t rho ≤ signedCost chi sigma t := by
  have hh := signed_ordinary_selected_bound chi hs t {rho} (by simpa using hr)
  exact (add_le_add le_rfl
    (reflectedKernel_le_singleton_mass chi hs t ⟨by linarith [hr.1], hr.2⟩ hz)).trans hh

theorem signed_quartic_selected_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) :
    24480 * reflectedKernel sigma rho.im rho ≤
      14379 * signedCost (1 : DirichletCharacter ℂ q) sigma 0 +
      24480 * signedCost chi sigma rho.im +
      14900 * signedCost (chi ^ 2) sigma (2 * rho.im) +
      6000 * signedCost (chi ^ 3) sigma (3 * rho.im) +
      1250 * signedCost (chi ^ 4) sigma (4 * rho.im) := by
  have hpos := quartic_stechkin_nonneg chi hs rho.im
  have hmain := signed_singleton_selected_bound chi hs rho.im hr hz
  have h0 := signed_ordinary_selected_bound (1 : DirichletCharacter ℂ q) hs 0 ∅ (by simp)
  have h2 := signed_ordinary_selected_bound (chi ^ 2) hs (2 * rho.im) ∅ (by simp)
  have h3 := signed_ordinary_selected_bound (chi ^ 3) hs (3 * rho.im) ∅ (by simp)
  have h4 := signed_ordinary_selected_bound (chi ^ 4) hs (4 * rho.im) ∅ (by simp)
  simp only [ordinaryMass, Finset.sum_empty, add_zero, f_eq_damped] at *
  linarith

end LiuWang.Proof.Campaign20260915.OriginalRegion
