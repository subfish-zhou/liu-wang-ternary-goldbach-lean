import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HWeightedContour

/-! The weighted argument principle for an arbitrary nonzero entire function. -/

set_option autoImplicit false

noncomputable section

open Complex Set

namespace LiuWang.Proof.SourceRoute.Density

def weightedKernel (f : ℂ → ℂ) (c s : ℂ) : ℂ :=
  (s - c) * logDeriv f s

theorem entire_meromorphicOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ s, analyticOrderAt f s ≠ ⊤) (s : ℂ) :
    meromorphicOrderAt f s = ((analyticOrderNatAt f s : ℤ) : WithTop ℤ) := by
  rw [(hf.analyticAt s).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (hfin s)]
  simp

theorem weighted_residue {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ s, analyticOrderAt f s ≠ ⊤) (c s : ℂ) :
    residue (weightedKernel f c) s = (s - c) * (analyticOrderNatAt f s : ℂ) := by
  have hr := Kadiri.residue_mul_eq_of_sub_principal_isBigO_one
    (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
      (hf.analyticAt s).meromorphicAt (entire_meromorphicOrder hf hfin s))
    (Ψ := fun z : ℂ => z - c) (by fun_prop)
  change residue (fun z : ℂ => (z - c) * logDeriv f z) s = _
  simpa only [mul_comm, Int.cast_natCast] using hr

theorem analytic_weightedKernel {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c s : ℂ} (hs : f s ≠ 0) : AnalyticAt ℂ (weightedKernel f c) s :=
  (analyticAt_id.sub analyticAt_const).mul
    ((hf.analyticAt s).deriv.div (hf.analyticAt s) hs)

theorem weighted_poles {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ s, analyticOrderAt f s ≠ ⊤) {c : ℂ} (hc : f c ≠ 0) (U : Set ℂ) :
    U ∩ {s | meromorphicOrderAt (weightedKernel f c) s < 0} =
      (MeromorphicOn.divisor f U).support := by
  have hm : MeromorphicOn f U := fun s _ => (hf.analyticAt s).meromorphicAt
  rw [← logDeriv_poles_eq_divisor_support hm hm.logDeriv
    (fun s _ => by rw [entire_meromorphicOrder hf hfin]; simp)]
  ext s
  by_cases hs : s = c
  · subst s
    have ha := analytic_weightedKernel hf (c := c) hc
    have hb : AnalyticAt ℂ (logDeriv f) c :=
      (hf.analyticAt c).deriv.div (hf.analyticAt c) hc
    simp only [mem_inter_iff, mem_ofPred_eq,
      not_lt.mpr ha.meromorphicOrderAt_nonneg, not_lt.mpr hb.meromorphicOrderAt_nonneg]
  · have he : meromorphicOrderAt (weightedKernel f c) s =
        meromorphicOrderAt (logDeriv f) s :=
      meromorphicOrderAt_mul_of_ne_zero
        (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - c) s) (sub_ne_zero.mpr hs)
    simp only [mem_inter_iff, mem_ofPred_eq, he]

theorem weighted_simple {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ s, analyticOrderAt f s ≠ ⊤) {c : ℂ} (hc : f c ≠ 0) (U : Set ℂ) :
    HasSimplePolesOn (weightedKernel f c) U := by
  have hm : MeromorphicOn f U := fun s _ => (hf.analyticAt s).meromorphicAt
  have hl := logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top hm hm.logDeriv
    (fun s _ => by rw [entire_meromorphicOrder hf hfin]; simp)
  intro s hs
  by_cases hsc : s = c
  · subst s
    exact le_trans (WithTop.coe_le_coe.mpr (by norm_num : (-1 : ℤ) ≤ 0))
      (analytic_weightedKernel hf (c := c) hc).meromorphicOrderAt_nonneg
  · change (-1 : ℤ) ≤ meromorphicOrderAt ((fun z : ℂ => z - c) * logDeriv f) s
    rw [meromorphicOrderAt_mul_of_ne_zero
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - c) s) (sub_ne_zero.mpr hsc)]
    exact hl s hs

theorem weighted_integrable {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c z w : ℂ}
    (hb : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleBorderIntegrable (weightedKernel f c) z w :=
  ContinuousOn.rectangleBorder_integrable
    (fun s hs => (analytic_weightedKernel hf (c := c) (hb s hs)).continuousAt.continuousWithinAt)

theorem weighted_rectangle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ s, analyticOrderAt f s ≠ ⊤) {c z w : ℂ} (hc : f c ≠ 0)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (weightedKernel f c) z w =
      ∑ s ∈ (divisor_support_rectangle_finite f z w).toFinset,
        (s - c) * (analyticOrderNatAt f s : ℂ) := by
  have hm0 : MeromorphicOn f univ := fun s _ => (hf.analyticAt s).meromorphicAt
  have hm : MeromorphicOn (weightedKernel f c) (Rectangle z w) :=
    fun s _ => (by fun_prop : MeromorphicAt (fun z : ℂ => z - c) s).mul
      (hm0.logDeriv s (mem_univ s))
  have hp := weighted_poles hf hfin hc (Rectangle z w)
  have hfinite : (Rectangle z w ∩
      {s | meromorphicOrderAt (weightedKernel f c) s < 0}).Finite := by
    rw [hp]
    exact divisor_support_rectangle_finite f z w
  have hn : Disjoint (RectangleBorder z w)
      {s | meromorphicOrderAt (weightedKernel f c) s < 0} := by
    rw [Set.disjoint_left]
    intro s hs hpole
    exact not_lt.mpr
      (analytic_weightedKernel hf (c := c) (hb s hs)).meromorphicOrderAt_nonneg hpole
  rw [RectangleIntegral'_eq_sumResiduesIn hre him hm hn hfinite
    (weighted_simple hf hfin hc _), hp, sumResiduesIn]
  have hD := divisor_support_rectangle_finite f z w
  have hsum : (∑' s : (MeromorphicOn.divisor f (Rectangle z w)).support,
      residue (weightedKernel f c) s) =
      ∑ s ∈ hD.toFinset, residue (weightedKernel f c) s := by
    let D := hD.toFinset
    change _ = ∑ s ∈ D, residue (weightedKernel f c) s
    have he : (MeromorphicOn.divisor f (Rectangle z w)).support = (D : Set ℂ) :=
      hD.coe_toFinset.symm
    rw [he, tsum_fintype, ← Finset.sum_coe_sort D]
    rfl
  rw [hsum]
  exact Finset.sum_congr rfl (fun s _ => weighted_residue hf hfin c s)

theorem weighted_rectangle_re {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ s, analyticOrderAt f s ≠ ⊤) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (RectangleIntegral' (weightedKernel f z) z w).re =
      ∑ s ∈ (divisor_support_rectangle_finite f z w).toFinset,
        (s.re - z.re) * (analyticOrderNatAt f s : ℝ) := by
  have hz : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  rw [weighted_rectangle hf hfin (hb z hz) hre him hb, Complex.re_sum]
  exact Finset.sum_congr rfl (fun s _ => by simp)

end LiuWang.Proof.SourceRoute.Density
