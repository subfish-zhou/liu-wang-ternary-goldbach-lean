import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal.Permutations

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

theorem reflection_fraction {a b c k s u : ℝ}
    (ha : 1 ≤ a) (has : a ≤ s) (hs : s ≤ 1.02)
    (hb : 0 < b) (hc : 0 < c)
    (hr : k * (b + c) ≤ s) (hp : s * a ≤ b * c)
    (hp1 : b * c ≤ 1.1) (hr2 : 5 ≤ (b + c) ^ 2) (hu : |u| ≤ 1) :
    k * (realKernel b u + realKernel c u) ≤ realKernel a u := by
  have ha0 : 0 < a := by linarith
  have ha1 : a ≤ 1.02 := has.trans hs
  have hu0 := sq_nonneg u
  have hu1 : u ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hu).1, (abs_le.mp hu).2]
  have hA : 0 < a ^ 2 + u ^ 2 := by positivity
  have hB : 0 < b ^ 2 + u ^ 2 := by positivity
  have hC : 0 < c ^ 2 + u ^ 2 := by positivity
  have h0 : 0 ≤ a * (b * c) * (b * c - s * a) :=
    mul_nonneg (by positivity) (by linarith)
  have hsq : a ^ 2 ≤ 1.0404 := by nlinarith
  have hmid : 0.6 ≤ a * ((b + c) ^ 2 - 2 * (b * c)) - s * (a ^ 2 + b * c) := by
    have hleft : 2.8 ≤ a * ((b + c) ^ 2 - 2 * (b * c)) := by
      nlinarith [mul_nonneg (show 0 ≤ a - 1 by linarith)
        (show 0 ≤ (b + c) ^ 2 - 2 * (b * c) by nlinarith)]
    have hright : s * (a ^ 2 + b * c) ≤ 1.02 * (1.0404 + 1.1) :=
      mul_le_mul hs (by linarith) (by positivity) (by norm_num)
    linarith
  have htail : 0 ≤ (0.6 + (a - s) * u ^ 2) * u ^ 2 := by
    apply mul_nonneg _ hu0
    nlinarith [mul_nonneg (show 0 ≤ s - a by linarith) (show 0 ≤ 1 - u ^ 2 by linarith)]
  have hmid' := mul_le_mul_of_nonneg_right hmid hu0
  have hpoly : 0 ≤ a * ((b ^ 2 + u ^ 2) * (c ^ 2 + u ^ 2)) -
      s * (a ^ 2 + u ^ 2) * (b * c + u ^ 2) := by
    nlinarith only [h0, htail, hmid']
  have hreplace := mul_le_mul_of_nonneg_right hr
    (show 0 ≤ (a ^ 2 + u ^ 2) * (b * c + u ^ 2) by positivity)
  unfold realKernel
  rw [div_add_div _ _ hB.ne' hC.ne', ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos hB hC) hA).mpr
  nlinarith only [hpoly, hreplace]

theorem reflected_near_no_loss {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    {rho : ℂ} (_hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (hgap : 1 - rho.re ≤ sigma - 1) {t : ℝ} (ht : |t - rho.im| ≤ 1) :
    realKernel (sigma - rho.re) (t - rho.im) ≤ reflectedKernel sigma t rho := by
  have he := stechkinSigma_equation sigma
  have hge := stechkinSigma_ge hs
  have hp : (stechkinSigma sigma - rho.re) * (stechkinSigma sigma - 1 + rho.re) =
      sigma ^ 2 + rho.re * (1 - rho.re) := by nlinarith
  have hratio := stechkin_ratio_sigma hs
  have htail := reflection_fraction
    (a := sigma - 1 + rho.re) (b := stechkinSigma sigma - rho.re)
    (c := stechkinSigma sigma - 1 + rho.re) (k := stechkinK) (s := sigma)
    (u := t - rho.im)
    (by linarith) (by linarith) hs1 (by linarith) (by linarith)
    (by nlinarith only [hratio])
    (by
      rw [hp]
      nlinarith [mul_nonneg (show 0 ≤ 1 - rho.re by linarith)
        (show 0 ≤ sigma + rho.re by linarith)])
    (by
      rw [hp]
      nlinarith [sq_nonneg (1 - rho.re)])
    (by nlinarith only [he, hs]) ht
  unfold reflectedKernel
  rw [dampedKernel_eq_realKernel, dampedKernel_eq_realKernel]
  simp only [sub_re, one_re, conj_re, sub_im, one_im, conj_im, sub_neg_eq_add, zero_add]
  rw [show sigma - (1 - rho.re) = sigma - 1 + rho.re by ring,
    show stechkinSigma sigma - (1 - rho.re) = stechkinSigma sigma - 1 + rho.re by ring]
  linarith

def poleDebit (sigma beta s : ℝ) : ℝ :=
  if |s| < 1 then realKernel (sigma - beta) s else 0

theorem poleDebit_le_reflected {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (hgap : 1 - rho.re ≤ sigma - 1) (t : ℝ) :
    poleDebit sigma rho.re (t - rho.im) ≤ reflectedKernel sigma t rho := by
  unfold poleDebit
  split_ifs with ht
  · exact reflected_near_no_loss hs hs1 hr hr1 hgap ht.le
  · exact dampedZeroKernel_pair_nonneg hs t ⟨by linarith, hr1.le⟩

theorem principal_pair_paid {d q : ℕ} [NeZero d] [NeZero q]
    {sigma y s beta eta : ℝ} (hdq : d ∣ q)
    (hs : 1 < sigma) (hs1 : sigma ≤ 1.02) (hq : (q : ℝ) ≤ y) (hy : |s| ≤ y / q)
    (hb : beta < 1) (he : eta < 1)
    (hgb : 1 - beta ≤ sigma - 1) (hge : 1 - eta ≤ sigma - 1)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| →
      gammaHalfDifference sigma t < stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference sigma t < 0.0615) :
    dampedLogDeriv (1 : DirichletCharacter ℂ d) sigma (stechkinSigma sigma) stechkinK s -
      poleDebit sigma beta s - poleDebit sigma eta s ≤ AllPrincipal.principalCost y + 0.4977 := by
  have heuler := principal_damped_euler_bound (q := d) hs s
  change _ ≤ zetaDamped sigma s + principalPrimeCost d sigma at heuler
  have hcost := lwd_2_3 d hs
  have hl := lwd_height_log hdq hq hy
  by_cases ht : |s| < 1
  · have hlow := lwd_2_21 hs (hgammaLow s ht).le
    have hpole := lwd_G_lemma_two (u := s) hs hb he hgb hge
    have hk : realKernel (sigma - 1) s = (1 / ((sigma : ℂ) - 1 + I * s)).re := by
      simp only [realKernel_eq_inverse_re, Complex.ofReal_sub, Complex.ofReal_one]
    rw [← hk] at hlow
    rw [max_eq_left ht.le, Real.log_one, add_zero] at hl
    have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
    simp only [poleDebit, if_pos ht, AllPrincipal.principalCost]
    linarith
  · have hh := zeta_high_unselected hs (by linarith) (le_of_not_gt ht)
      (hgammaHigh s (le_of_not_gt ht)).le
    rw [max_eq_right (le_of_not_gt ht)] at hl
    have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
    simp only [poleDebit, if_neg ht, sub_zero, AllPrincipal.principalCost]
    linarith

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
