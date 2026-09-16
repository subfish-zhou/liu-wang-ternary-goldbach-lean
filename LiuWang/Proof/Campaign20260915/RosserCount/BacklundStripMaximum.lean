import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyPhiEdges
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false
noncomputable section

open Complex Set Filter Bornology Metric
open scoped Topology
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlundStripPhi_damped_bound {z : ℂ}
    (hz : 0 ≤ z.re) (hz' : z.re ≤ 1) (hzt : 50 ≤ z.im)
    {ε : ℝ} (hε : 0 < ε) :
    ‖backlundStripPhi z * Complex.exp ((ε : ℂ) * (z ^ 2 - 1))‖ ≤ 1 := by
  obtain ⟨C, hC, hgrowth⟩ := exists_backlundStripPhi_fifty_growth
  let A := |Real.log C| + Real.pi / 2 + 1
  let R := 51 + |z.im| + |A / ε|
  have hR : 50 < R := by dsimp [R]; linarith [abs_nonneg z.im, abs_nonneg (A / ε)]
  have hR1 : 1 ≤ R := by linarith
  have hzR : z.im ≤ R := by dsimp [R]; linarith [le_abs_self z.im, abs_nonneg (A / ε)]
  have hAR : A / ε ≤ R := by dsimp [R]; linarith [le_abs_self (A / ε), abs_nonneg z.im]
  have hAR' : A ≤ ε * R := by
    have h := (div_le_iff₀ hε).mp hAR
    nlinarith
  have htop : Real.log C + Real.pi * R / 2 - ε * R ^ 2 ≤ 0 := by
    have h := mul_nonneg (sub_nonneg.mpr hAR') (by linarith : 0 ≤ R)
    have h' := mul_le_mul_of_nonneg_left hR1 (abs_nonneg (Real.log C))
    dsimp [A] at h
    nlinarith [le_abs_self (Real.log C)]
  let g : ℂ → ℂ := fun w => backlundStripPhi w * Complex.exp ((ε : ℂ) * (w ^ 2 - 1))
  have hnorm (w : ℂ) :
      ‖g w‖ = ‖backlundStripPhi w‖ * Real.exp (ε * (w.re ^ 2 - w.im ^ 2 - 1)) := by
    simp only [g, norm_mul, Complex.norm_exp, sub_re, one_re,
      pow_two, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have hfactor (w : ℂ) (hw : w.re ∈ Icc 0 1) :
      Real.exp (ε * (w.re ^ 2 - w.im ^ 2 - 1)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hε.le (by nlinarith [sq_nonneg w.im, hw.1, hw.2])
  have hd : DiffContOnCl ℂ g (Ioo 0 1 ×ℂ Ioo 50 R) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_Ioo hR.ne] at hw
    have hd := backlundStripPhi_differentiableAt hw.1.1 hw.1.2 (by linarith [hw.2.1])
    exact (hd.mul (by fun_prop)).differentiableWithinAt
  apply norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (0 : ℝ) 1).reProdIm (isBounded_Ioo (50 : ℝ) R)) hd
  · intro w hw
    rw [frontier_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_Ioo hR.ne, frontier_Ioo (by norm_num : (0 : ℝ) < 1),
      frontier_Ioo hR] at hw
    have hrect : w.re ∈ Icc 0 1 ∧ w.im ∈ Icc 50 R := by
      rcases hw with hw | hw
      · refine ⟨hw.1, ?_⟩
        rcases hw.2 with hb | ht
        · rw [hb]; exact ⟨le_rfl, hR.le⟩
        · rw [ht]; exact ⟨hR.le, le_rfl⟩
      · refine ⟨?_, hw.2⟩
        rcases hw.1 with hl | hr
        · rw [hl]; norm_num
        · rw [hr]; norm_num
    by_cases hwt : w.im = R
    · have hg := hgrowth w hrect.1.1 hrect.1.2 hrect.2.1
      rw [hnorm]
      calc
        _ ≤ (C * Real.exp (Real.pi * w.im / 2)) *
            Real.exp (ε * (w.re ^ 2 - w.im ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
        _ ≤ (C * Real.exp (Real.pi * R / 2)) * Real.exp (-ε * R ^ 2) := by
          rw [hwt]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          have hm := mul_nonpos_of_nonneg_of_nonpos hε.le
            (show w.re ^ 2 - 1 ≤ 0 by nlinarith [hrect.1.1, hrect.1.2])
          nlinarith
        _ = Real.exp (Real.log C + Real.pi * R / 2 - ε * R ^ 2) := by
          rw [Real.exp_sub, Real.exp_add, Real.exp_log hC, neg_mul, Real.exp_neg]
          ring
        _ ≤ 1 := Real.exp_le_one_iff.mpr htop
    · have hb : ‖backlundStripPhi w‖ < 1 := by
        rcases hw with hw | hw
        · exact backlundStripPhi_fifty_bottom hw.1.1 hw.1.2
            (hw.2.resolve_right hwt)
        · exact backlundStripPhi_vertical_fifty hw.1 hw.2.1
      rw [hnorm]
      exact mul_le_one₀ hb.le (by positivity) (hfactor w hrect.1)
  · rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioo hR.ne]
    exact ⟨⟨hz, hz'⟩, ⟨hzt, hzR⟩⟩

theorem backlundStripPhi_le_one {z : ℂ}
    (hz : 0 ≤ z.re) (hz' : z.re ≤ 1) (hzt : 50 ≤ z.im) :
    ‖backlundStripPhi z‖ ≤ 1 := by
  let f : ℝ → ℝ := fun ε => ‖backlundStripPhi z * Complex.exp ((ε : ℂ) * (z ^ 2 - 1))‖
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hl : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 ‖backlundStripPhi z‖) := by
    simpa [f] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact backlundStripPhi_damped_bound hz hz' hzt hε

theorem backlundStripPhi_lt_one {z : ℂ}
    (hz : 0 ≤ z.re) (hz' : z.re ≤ 1) (hzt : 50 ≤ z.im) :
    ‖backlundStripPhi z‖ < 1 := by
  by_cases he : z.re = 0 ∨ z.re = 1
  · exact backlundStripPhi_vertical_fifty he hzt
  by_cases ht : z.im = 50
  · exact backlundStripPhi_fifty_bottom hz hz' ht
  have hzi : z ∈ Ioo 0 1 ×ℂ Ioi (50 : ℝ) := by
    exact ⟨⟨lt_of_le_of_ne hz (Ne.symm fun h => he (Or.inl h)),
      lt_of_le_of_ne hz' (fun h => he (Or.inr h))⟩, lt_of_le_of_ne hzt (Ne.symm ht)⟩
  have hd : DiffContOnCl ℂ backlundStripPhi (Ioo 0 1 ×ℂ Ioi (50 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi] at hw
    have hwt : 50 ≤ w.im := hw.2
    exact (backlundStripPhi_differentiableAt hw.1.1 hw.1.2 (by linarith)).differentiableWithinAt
  have hconv : Convex ℝ (Ioo 0 1 ×ℂ Ioi (50 : ℝ)) :=
    ((convex_Ioo (0 : ℝ) 1).linear_preimage reCLM.toLinearMap).inter
      ((convex_Ioi (50 : ℝ)).linear_preimage imCLM.toLinearMap)
  rcases (backlundStripPhi_le_one hz hz' hzt).lt_or_eq with h | h
  · exact h
  have hm : IsMaxOn (norm ∘ backlundStripPhi) (Ioo 0 1 ×ℂ Ioi (50 : ℝ)) z := by
    intro w hw
    change ‖backlundStripPhi w‖ ≤ ‖backlundStripPhi z‖
    rw [h]
    exact backlundStripPhi_le_one hw.1.1.le hw.1.2.le hw.2.le
  have hc := norm_eqOn_closure_of_isPreconnected_of_isMaxOn
    hconv.isPreconnected (IsOpen.reProdIm isOpen_Ioo isOpen_Ioi) hd hzi hm
  have hb : horizontalAt 50 (1 / 2) ∈ closure (Ioo 0 1 ×ℂ Ioi (50 : ℝ)) := by
    rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi]
    norm_num [mem_reProdIm, horizontalAt]
  have heq := hc hb
  change ‖backlundStripPhi (horizontalAt 50 (1 / 2))‖ = ‖backlundStripPhi z‖ at heq
  have hl := backlundStripPhi_fifty_bottom
    (s := horizontalAt 50 (1 / 2)) (by norm_num [horizontalAt])
      (by norm_num [horizontalAt]) (by simp [horizontalAt])
  linarith

#print axioms backlundStripPhi_damped_bound
#print axioms backlundStripPhi_le_one
#print axioms backlundStripPhi_lt_one

end LiuWang.Proof.Campaign20260915.RosserCount
