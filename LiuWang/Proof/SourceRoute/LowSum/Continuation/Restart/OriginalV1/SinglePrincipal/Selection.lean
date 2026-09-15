import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal.Products

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

theorem primitive_selected_reflections {d : ℕ} [NeZero d]
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) (s : Finset ℂ)
    (hr : ∀ z ∈ s, 1 / 2 < z.re ∧ z.re < 1)
    (hz : ∀ z ∈ s, chi.LFunction z = 0) :
    (∑ z ∈ s, reflectedKernel sigma t z) ≤ primitiveZeroSum chi sigma t := by
  have hm := primitive_ordinary_mass_le hc hp hs t s (fun z h => (hr z h).1)
  apply le_trans _ hm
  apply Finset.sum_le_sum
  intro z h
  have ho : (1 : ℝ) ≤ analyticOrderNatAt chi.LFunction z := by
    exact_mod_cast ordinary_zero_order_pos chi
      (by intro he; simpa [he] using (hr z h).2) (hz z h)
  have hn : 0 ≤ reflectedKernel sigma t z :=
    dampedZeroKernel_pair_nonneg hs t ⟨by linarith [(hr z h).1], (hr z h).2.le⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ho hn

theorem primitive_single_near {d q : ℕ} [NeZero d] [NeZero q]
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {x sigma : ℝ} (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re ∧ rho.re < 1) (ht : 1 / 2 < tau.re ∧ tau.re < 1)
    (hzr : chi.LFunction rho = 0) (hzt : chi.LFunction tau = 0)
    (hne : rho ≠ tau) (hy : |rho.im| ≤ x / q) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK rho.im ≤
      nonprincipalCost x - 1 / (sigma - rho.re) -
      nearDebit sigma tau.re (rho.im - tau.im) := by
  have hm := primitive_selected_reflections chi hc hp hs rho.im {rho, tau}
    (by simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
      And.intro hr ht)
    (by simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
      And.intro hzr hzt)
  simp only [Finset.sum_pair hne] at hm
  have h0 := selected_pair_dominates hs ⟨by linarith [hr.1], hr.2⟩
  change _ ≤ reflectedKernel sigma rho.im rho at h0
  have h1 := nearDebit_le_reflected hs hs1 ht.1 ht.2 rho.im
  have hb := primitive_full_zero_sum_bound hc hp hs (by linarith : sigma ≤ 23 / 20) rho.im
  have hl := mul_le_mul_of_nonneg_left (lwd_height_log hdq hq hy) conductorCoeff_bounds.1
  unfold nonprincipalCost
  nlinarith only [hm, h0, h1, hb, hl]

theorem primitive_off_near {d q : ℕ} [NeZero d] [NeZero q]
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {x sigma t : ℝ} (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho : ℂ} (hr : 1 / 2 < rho.re ∧ rho.re < 1)
    (hz : chi.LFunction rho = 0) (hy : |t| ≤ x / q) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      nonprincipalCost x - nearDebit sigma rho.re (t - rho.im) := by
  have hm := primitive_selected_reflections chi hc hp hs t {rho}
    (by simpa only [Finset.mem_singleton, forall_eq] using hr)
    (by simpa only [Finset.mem_singleton, forall_eq] using hz)
  simp only [Finset.sum_singleton] at hm
  have h1 := nearDebit_le_reflected hs hs1 hr.1 hr.2 t
  have hb := primitive_full_zero_sum_bound hc hp hs (by linarith : sigma ≤ 23 / 20) t
  have hl := mul_le_mul_of_nonneg_left (lwd_height_log hdq hq hy) conductorCoeff_bounds.1
  unfold nonprincipalCost
  nlinarith only [hm, h1, hb, hl]

theorem rs_log_gap {q : ℕ} [NeZero q] {x t : ℝ}
    (ht : 1894438 ≤ |t|) (hy : |t| ≤ x / q) :
    Real.log q + 6 ≤ Real.log x := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hmul : (1024 : ℝ) * q ≤ x := (le_div_iff₀ hq).mp (by linarith)
  have hl := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 1024) hq) hmul
  rw [Real.log_mul (by norm_num) hq.ne',
    show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith [Real.log_two_gt_d9]

theorem principal_corrected_pair {d q : ℕ} [NeZero d] [NeZero q]
    {sigma y s beta eta : ℝ} (hdq : d ∣ q)
    (hs : 1 < sigma) (hs1 : sigma < 1.15) (hq : (q : ℝ) ≤ y)
    (hgap : Real.log q + 6 ≤ Real.log y) (hy : |s| ≤ y / q)
    (hb : beta < 1) (he : eta < 1)
    (hgb : 1 - beta ≤ sigma - 1) (hge : 1 - eta ≤ sigma - 1)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| →
      gammaHalfDifference sigma t < stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference sigma t < 0.0615) :
    dampedLogDeriv (1 : DirichletCharacter ℂ d) sigma (stechkinSigma sigma) stechkinK s -
      nearDebit sigma beta s - nearDebit sigma eta s ≤ principalCost y + 0.4977 := by
  have heuler := principal_damped_euler_bound (q := d) hs s
  change _ ≤ zetaDamped sigma s + principalPrimeCost d sigma at heuler
  have hcost := lwd_2_3 d hs
  by_cases ht : |s| < 1
  · have hlow := lwd_2_21 hs (hgammaLow s ht).le
    have hpole := lwd_G_lemma_two (u := s) hs hb he hgb hge
    have hk : realKernel (sigma - 1) s = (1 / ((sigma : ℂ) - 1 + I * s)).re := by
      simp only [realKernel_eq_inverse_re, Complex.ofReal_sub, Complex.ofReal_one]
    rw [← hk] at hlow
    have hd : Real.log d ≤ Real.log q := Real.log_le_log
      (by exact_mod_cast NeZero.pos d) (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdq)
    have hm := mul_le_mul_of_nonneg_left (show Real.log d + 6 ≤ Real.log y by linarith)
      conductorCoeff_bounds.1
    have hroot : Real.sqrt 5 ≤ 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
    simp only [nearDebit, if_pos ht, offDebit, principalCost]
    nlinarith only [heuler, hcost, hlow, hpole, hm, hroot, lwd_kappa_bounds.1]
  · have hh := zeta_high_unselected hs hs1 (le_of_not_gt ht)
      (hgammaHigh s (le_of_not_gt ht)).le
    have hl := lwd_height_log hdq hq hy
    rw [max_eq_right (le_of_not_gt ht)] at hl
    have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
    simp only [nearDebit, if_neg ht, sub_zero, principalCost]
    nlinarith only [heuler, hcost, hh, hm]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
