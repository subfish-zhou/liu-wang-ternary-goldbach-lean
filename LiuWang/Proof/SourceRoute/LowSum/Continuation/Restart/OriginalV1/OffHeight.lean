import LiuWang.Proof.MultiZeroRepulsion.Continuation.OffHeight

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1

theorem lwd_reflected_realKernel {sigma beta u : ℝ}
    (hs : 1 < sigma) (hs1 : sigma < 1.15) (hb : 1 / 2 ≤ beta) (hb1 : beta < 1)
    (hu : |u| ≤ 1) :
    2 / 5 ≤ realKernel (sigma - 1 + beta) u := by
  have ha : 1 / 2 ≤ sigma - 1 + beta := by linarith
  have ha1 : sigma - 1 + beta ≤ 2 := by linarith
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hu).1, (abs_le.mp hu).2]
  have hprod := mul_nonneg (show 0 ≤ sigma - 1 + beta - 1 / 2 by linarith)
    (show 0 ≤ 2 - (sigma - 1 + beta) by linarith)
  dsimp [realKernel]
  apply (le_div_iff₀ (by nlinarith [sq_nonneg u])).mpr
  nlinarith

theorem lwd_damped_inverse_bounds {sigma beta : ℝ}
    (hs : 1 < sigma) (hb : 1 / 2 ≤ beta) (hb1 : beta < 1) :
    stechkinK / (stechkinSigma sigma - 1 + beta) ≤ 2 / 5 ∧
      stechkinK / (stechkinSigma sigma - beta) ≤ (5 + Real.sqrt 5) / 10 := by
  have hr : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have ht := stechkinSigma_ge hs
  have he := stechkinSigma_equation sigma
  have ht0 : (1 + Real.sqrt 5) / 2 ≤ stechkinSigma sigma := by
    nlinarith
  have hk : stechkinK = Real.sqrt 5 / 5 := by
    dsimp [stechkinK]
    apply (div_eq_div_iff hr.ne' (by norm_num)).mpr
    nlinarith
  rw [hk]
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < stechkinSigma sigma - 1 + beta)).mpr
    linarith
  · apply (div_le_iff₀ (by linarith : 0 < stechkinSigma sigma - beta)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 5 + Real.sqrt 5 by positivity)
      (show 0 ≤ stechkinSigma sigma - beta - (Real.sqrt 5 - 1) / 2 by linarith)]

theorem lwd_2_16_kernel {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho : ℂ} (hr : 1 / 2 ≤ rho.re) (hr1 : rho.re < 1) {t : ℝ}
    (ht : |t - rho.im| ≤ 1) :
    realKernel (sigma - rho.re) (t - rho.im) - (5 + Real.sqrt 5) / 10 ≤
      reflectedKernel sigma t rho := by
  have hge := stechkinSigma_ge hs
  have h1 := mul_le_mul_of_nonneg_left
    (realKernel_le_inverse (show 0 < stechkinSigma sigma - rho.re by linarith)
      (t - rho.im)) stechkinK_mem.1
  have h2 := mul_le_mul_of_nonneg_left
    (realKernel_le_inverse (show 0 < stechkinSigma sigma - 1 + rho.re by linarith)
      (t - rho.im)) stechkinK_mem.1
  have hb := lwd_damped_inverse_bounds hs hr hr1
  have hl := lwd_reflected_realKernel hs hs1 hr hr1 ht
  simp only [mul_one_div] at h1 h2
  unfold reflectedKernel
  rw [dampedKernel_eq_realKernel, dampedKernel_eq_realKernel]
  simp only [sub_re, one_re, conj_re, sub_im, one_im, conj_im, sub_neg_eq_add, zero_add]
  rw [show sigma - (1 - rho.re) = sigma - 1 + rho.re by ring,
    show stechkinSigma sigma - (1 - rho.re) = stechkinSigma sigma - 1 + rho.re by ring]
  linarith [hb.1, hb.2]

theorem lwd_2_16_mass {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15) (t : ℝ)
    (v w : Finset ℂ) (hvw : Disjoint v w)
    (hv : ∀ rho ∈ v, 1 / 2 ≤ rho.re ∧ rho.re < 1 ∧ rho.im = t)
    (hw : ∀ rho ∈ w, 1 / 2 ≤ rho.re ∧ rho.re < 1 ∧ |t - rho.im| ≤ 1) :
    (∑ rho ∈ v, (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re)) +
      (∑ rho ∈ w, (analyticOrderNatAt chi.LFunction rho : ℝ) *
        realKernel (sigma - rho.re) (t - rho.im)) -
      (5 + Real.sqrt 5) / 10 * (∑ rho ∈ w, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      ordinaryMass chi sigma t (v ∪ w) := by
  have hvb : (∑ rho ∈ v, (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re)) ≤
      ordinaryMass chi sigma t v := by
    apply Finset.sum_le_sum
    intro rho h
    obtain ⟨hr, hr1, ht⟩ := hv rho h
    have hh := mul_le_mul_of_nonneg_left
      (selected_pair_dominates hs ⟨by linarith, hr1⟩)
      (Nat.cast_nonneg (analyticOrderNatAt chi.LFunction rho) : (0 : ℝ) ≤ _)
    simpa only [mul_one_div, ht, reflectedKernel] using hh
  have hwb := Finset.sum_le_sum (s := w) (fun rho h =>
    mul_le_mul_of_nonneg_left
      (lwd_2_16_kernel hs hs1 (hw rho h).1 (hw rho h).2.1 (hw rho h).2.2)
      (Nat.cast_nonneg (analyticOrderNatAt chi.LFunction rho) : (0 : ℝ) ≤ _))
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hwb
  have hm : ordinaryMass chi sigma t (v ∪ w) =
      ordinaryMass chi sigma t v + ordinaryMass chi sigma t w := by
    exact Finset.sum_union hvw
  rw [hm]
  change _ ≤ ordinaryMass chi sigma t w at hwb
  nlinarith only [hvb, hwb]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
