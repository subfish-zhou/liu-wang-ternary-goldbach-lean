import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.HArgument

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory
open scoped Interval

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def rightHLog (y U t : ℝ) : ℂ :=
  rightLog (entireH y) 2 U t - 2 * rightLog poleFactor 2 U t

theorem rightHLog_data {y : ℝ} (hy : 5 ≤ y) (U : ℝ) :
    ContinuousOn (rightHLog y U) [[-U, U]] ∧
      ∀ t ∈ [[-U, U]], Complex.exp (rightHLog y U t) = H y ((2 : ℂ) + t * I) := by
  have he : ∀ t ∈ [[-U, U]], entireH y (((2 : ℝ) : ℂ) + t * I) ≠ 0 :=
    fun t _ => entireH_two_line_ne_zero (by linarith) (by simp)
  have hp : ∀ t ∈ [[-U, U]], poleFactor (((2 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t _ hz
    have h := congrArg Complex.re hz
    norm_num [poleFactor] at h
  refine ⟨(lineLog_continuousOn (differentiable_entireH y) he).sub
    (continuousOn_const.mul (lineLog_continuousOn poleFactor_differentiable hp)), ?_⟩
  intro t ht
  have eh := rightLog_exp (differentiable_entireH y) he ht
  have ph := rightLog_exp poleFactor_differentiable hp ht
  have ps := hp t ht
  have hexp : Complex.exp (2 * rightLog poleFactor 2 U t) =
      Complex.exp (rightLog poleFactor 2 U t) ^ 2 := Complex.exp_nat_mul _ 2
  rw [rightHLog, Complex.exp_sub, hexp, eh, ph,
    entireH_eq (sub_ne_zero.mp ps)]
  change (poleFactor ((2 : ℂ) + t * I) ^ 2 * H y ((2 : ℂ) + t * I)) /
    poleFactor ((2 : ℂ) + t * I) ^ 2 = _
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 ps)

theorem rightHLog_variation {y U : ℝ} (hy : 5 ≤ y) (hU : 0 ≤ U) :
    |(rightHLog y U U).im - (rightHLog y U (-U)).im| ≤ Real.pi := by
  have hdata := rightHLog_data hy U
  have hA : ContinuousOn (fun t : ℝ => (rightHLog y U t).im) (Icc (-U) U) := by
    simpa only [uIcc_of_le (show -U ≤ U by linarith), Function.comp_def] using
      Complex.continuous_im.comp_continuousOn hdata.1
  have hcos : ∀ t ∈ Icc (-U) U, Real.cos (rightHLog y U t).im = 0 → (t : ℂ) ∈ (∅ : Finset ℂ) := by
    intro t ht hz
    have he := congrArg Complex.re (hdata.2 t
      (by simpa [uIcc_of_le (show -U ≤ U by linarith)] using ht))
    rw [Complex.exp_re, hz, mul_zero] at he
    have hr := H_re_two_lower (by linarith : 1 < y) t
    have hq : 4 / (y - 1) ^ 2 ≤ 1 / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < y - 1))).mpr
      nlinarith
    exfalso
    linarith
  simpa using argument_variation_le (by linarith : -U ≤ U) hA ∅ hcos

theorem horizontalLog_right_anchor (y U h : ℝ) :
    HhorizontalLog y 2 U h 2 = rightHLog y U h := by
  simp only [HhorizontalLog, horizontalLog, lineLog_anchor, rightHLog]

theorem argumentCost_card_bound {y a U : ℝ} (hy : 5 ≤ y)
    (ha : a < 1) (hU : 0 < U) (hrU : 2 - a < U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) :
    argumentCost y a U ≤ (2 - a) * Real.pi *
      (2 * (reflectedZeros y U (2 - a)).card + 3 : ℝ) := by
  have hp := horizontal_argument_centered_integral hy ha hU hrU hn (Or.inr rfl)
  have hm := horizontal_argument_centered_integral hy ha hU hrU hn (Or.inl rfl)
  rw [horizontalLog_right_anchor] at hp hm
  have hr := rightHLog_variation hy hU.le
  have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hr).2
    (show 0 ≤ 2 - a by linarith)
  unfold argumentCost
  nlinarith [(abs_le.mp hp).2, (abs_le.mp hm).1]

theorem reflected_card_le_divisor {y U r : ℝ} (hy : 5 ≤ y)
    (hr : 0 ≤ r) (hrU : r < U) :
    ((reflectedZeros y U r).card : ℝ) ≤
      ((∑ᶠ s, MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r) s : ℤ) : ℝ) := by
  classical
  let D := MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r)
  have hsum : (∑ᶠ s, D s) = ∑ s ∈ reflectedZeros y U r, D s :=
    finsum_eq_sum_of_support_subset _ (fun s hs =>
      (D.finiteSupport (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mpr hs)
  have hcard : ((reflectedZeros y U r).card : ℤ) ≤ ∑ᶠ s, D s := by
    rw [hsum]
    calc
      ((reflectedZeros y U r).card : ℤ) = ∑ _s ∈ reflectedZeros y U r, (1 : ℤ) := by simp
      _ ≤ ∑ s ∈ reflectedZeros y U r, D s := by
        apply Finset.sum_le_sum
        intro s hs
        have hsm := (D.finiteSupport (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mp hs
        have he := reflectedH_divisor_actual_order hy hr le_rfl hrU (D.supportWithinDomain hsm)
        have hn : D s ≠ 0 := hsm
        change D s = _ at he
        rw [he] at hn ⊢
        have hp : (0 : ℤ) ≤ (analyticOrderNatAt (reflectedH y U) s : ℤ) := Int.natCast_nonneg _
        omega
  exact_mod_cast hcard

theorem argumentCost_jensen_bound {y a U R : ℝ} (hy : 10000 ≤ y)
    (ha : a < 1) (haR : 2 - a < R) (hRU : R < U) (hR : R ≤ 3 / 2)
    (hwin : |U - y| + R ≤ 3 / 2)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) :
    argumentCost y a U ≤ (2 - a) * Real.pi *
      (2 * (Real.log (2 * (1 + windowMajorant y (2 - R)) / (2 - 8 / (y - 1) ^ 2)) /
        Real.log (R / (2 - a))) + 3) := by
  have hr : 0 < 2 - a := by linarith
  have hcard := (reflected_card_le_divisor (by linarith : 5 ≤ y) hr.le
    (haR.trans hRU)).trans (reflectedH_jensen_explicit hy hr haR hRU hR hwin)
  apply (argumentCost_card_bound (by linarith : 5 ≤ y) ha (by linarith)
    (haR.trans hRU) hn).trans
  exact mul_le_mul_of_nonneg_left (by linarith : _ ≤ _)
    (mul_nonneg hr.le Real.pi_pos.le)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
