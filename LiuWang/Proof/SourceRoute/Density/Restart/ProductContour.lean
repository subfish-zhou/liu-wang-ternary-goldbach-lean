import LiuWang.Proof.SourceRoute.Density.Restart.FamilyProduct

/-! The actual product contour equals the sum of the character contours, including multiplicity. -/

set_option autoImplicit false

noncomputable section

open Complex Finset Set MeasureTheory
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.SourceRoute.Density.Restart

theorem rectangleIntegral_finset_sum {ι : Type*} (S : Finset ι) (g : ι → ℂ → ℂ) (z w : ℂ)
    (hg : ∀ i ∈ S, RectangleBorderIntegrable (g i) z w) :
    RectangleIntegral' (fun s => ∑ i ∈ S, g i s) z w =
      ∑ i ∈ S, RectangleIntegral' (g i) z w := by
  unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hg i hi).1),
    intervalIntegral.integral_finsetSum (fun i hi => (hg i hi).2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (hg i hi).2.2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (hg i hi).2.2.2)]
  simp only [smul_sum, smul_sub, smul_add, sum_sub_distrib, sum_add_distrib]

theorem product_logDeriv_sum (q : ℕ) [NeZero q] (X : ℝ) {s : ℂ}
    (hs : ∀ chi ∈ nonprincipalCharacters q, H chi X s ≠ 0) :
    logDeriv (familyProduct q X) s =
      ∑ chi ∈ nonprincipalCharacters q, logDeriv (H chi X) s :=
  logDeriv_prod hs (fun chi hc => differentiable_H ((mem_nonprincipalCharacters chi).mp hc) X s)

theorem product_weighted_contour_sum (q : ℕ) [NeZero q] (X : ℝ) {z w : ℂ}
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder z w, H chi X s ≠ 0) :
    RectangleIntegral' (weightedKernel (familyProduct q X) z) z w =
      ∑ chi ∈ nonprincipalCharacters q, RectangleIntegral' (weightedKernel (H chi X) z) z w := by
  calc
    _ = RectangleIntegral' (fun s => ∑ chi ∈ nonprincipalCharacters q,
        weightedKernel (H chi X) z s) z w := by
      apply RectangleIntegral'_congr
      intro s hs
      simp only [weightedKernel, product_logDeriv_sum q X (fun chi hc => hb chi hc s hs), mul_sum]
    _ = _ := rectangleIntegral_finset_sum _ _ z w (fun chi hc =>
      weighted_integrable (differentiable_H ((mem_nonprincipalCharacters chi).mp hc) X) (hb chi hc))

theorem closed_count_product_contour (q : ℕ) [NeZero q] {X alpha T a U d : ℝ}
    (hX : 3 < X) (ha : a ≤ 2) (hU : 0 ≤ U) (hTU : T ≤ U)
    (hd : 0 ≤ d) (hgap : a + d ≤ alpha)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    d * (nonprincipalCount q alpha T : ℝ) ≤
      (RectangleIntegral' (weightedKernel (familyProduct q X) ((a : ℂ) - U * I))
        ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re := by
  have h := closed_count_weighted_le q hX ha hU hTU hd hgap hb
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [weightedContour, ← mul_div_assoc] at h
  rw [product_weighted_contour_sum q X hb, Complex.re_sum]
  exact (div_le_div_iff_of_pos_right hp).mp h

def productHorizontal (q : ℕ) [NeZero q] (X a U : ℝ) : ℝ :=
  (∫ x in a..2, (horizontalLog (familyProduct q X) 2 U U x).im) -
    (∫ x in a..2, (horizontalLog (familyProduct q X) 2 U (-U) x).im)

theorem product_log_norm (q : ℕ) [NeZero q] (X : ℝ) {s : ℂ}
    (hs : ∀ chi ∈ nonprincipalCharacters q, H chi X s ≠ 0) :
    Real.log ‖familyProduct q X s‖ =
      ∑ chi ∈ nonprincipalCharacters q, Real.log ‖H chi X s‖ := by
  rw [familyProduct, norm_prod, Real.log_prod]
  exact fun chi hc => norm_ne_zero_iff.mpr (hs chi hc)

theorem product_vertical_difference (q : ℕ) [NeZero q] (X : ℝ) {a U : ℝ}
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    (∫ t in -U..U, Real.log ‖familyProduct q X ((a : ℂ) + t * I)‖) -
        (∫ t in -U..U, Real.log ‖familyProduct q X ((2 : ℂ) + t * I)‖) =
      (q.totient : ℝ) * logSideDifference q X a U := by
  have he (sigma : ℝ) (hside : sigma = a ∨ sigma = 2) :
      (∫ t in -U..U, Real.log ‖familyProduct q X ((sigma : ℂ) + t * I)‖) =
        ∑ chi ∈ nonprincipalCharacters q, ∫ t in -U..U, Real.log ‖H chi X ((sigma : ℂ) + t * I)‖ := by
    calc
      _ = ∫ t in -U..U, ∑ chi ∈ nonprincipalCharacters q,
          Real.log ‖H chi X ((sigma : ℂ) + t * I)‖ := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply product_log_norm
        intro chi hc
        apply hb chi hc
        rcases hside with rfl | rfl
        · simp [RectangleBorder, mem_reProdIm, ht]
        · simp [RectangleBorder, mem_reProdIm, ht]
      _ = _ := intervalIntegral.integral_finsetSum (fun chi hc =>
        log_H_vertical_integrable ((mem_nonprincipalCharacters chi).mp hc) X sigma U)
  have htwo := he 2 (Or.inr rfl)
  simp only [ofReal_ofNat] at htwo
  rw [he a (Or.inl rfl), htwo, ← sum_sub_distrib]
  have hp : (q.totient : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))
  unfold logSideDifference
  rw [mul_div_cancel₀ _ hp]
  apply sum_congr rfl
  intro chi hc
  have hi := intervalIntegral.integral_sub
    (log_H_vertical_integrable ((mem_nonprincipalCharacters chi).mp hc) X a U)
    (log_H_vertical_integrable ((mem_nonprincipalCharacters chi).mp hc) X 2 U)
  simpa only [ofReal_ofNat] using hi.symm

theorem closed_count_product_littlewood (q : ℕ) [NeZero q] {X alpha T a U d : ℝ}
    (hX : 3 < X) (ha : a ≤ 2) (hU : 0 ≤ U) (hTU : T ≤ U)
    (hd : 0 ≤ d) (hgap : a + d ≤ alpha)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    2 * Real.pi * d * (nonprincipalCount q alpha T : ℝ) ≤
      (q.totient : ℝ) * logSideDifference q X a U + productHorizontal q X a U := by
  have hp : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q X s ≠ 0 :=
    fun s hs => familyProduct_ne_zero (fun chi hc => hb chi hc s hs)
  have hl := rectangle_littlewood_entire (familyProduct_differentiable q X)
    (a := a) (b := 2) (c := -U) (d := U) (by simpa [sub_eq_add_neg] using hp)
  simp only [ofReal_neg, ofReal_ofNat, neg_mul, ← sub_eq_add_neg] at hl
  rw [product_vertical_difference q X hb] at hl
  have h := mul_le_mul_of_nonneg_left
    (closed_count_product_contour q hX ha hU hTU hd hgap hb) (by positivity : 0 ≤ 2 * Real.pi)
  change _ ≤ 2 * Real.pi *
    (RectangleIntegral' (fun s => (s - ((a : ℂ) - U * I)) * logDeriv (familyProduct q X) s)
      ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re at h
  rw [hl] at h
  simpa only [productHorizontal, mul_assoc, sub_eq_add_neg, add_assoc] using h

end LiuWang.Proof.SourceRoute.Density.Restart
