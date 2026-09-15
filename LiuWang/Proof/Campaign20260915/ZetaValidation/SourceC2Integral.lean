import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelAffineTails

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsC2RightIntegrand (s : ℂ) (eta : ℝ) (m : ℕ) (y : ℝ) : ℂ :=
  rsDescentDirection * rsHankelKernel s m (rsDescentPoint eta y)

def rsC2LeftIntegrand (s : ℂ) (eta : ℝ) (m : ℕ) (r : ℝ) : ℂ :=
  rsC2LeftDirection eta m * rsHankelKernel s m (rsC2LeftPoint eta m r)

def rsSourceC2 (s : ℂ) (eta : ℝ) (m : ℕ) : ℂ :=
  -(∫ y : ℝ in Ioi (-eta / 2), rsC2RightIntegrand s eta m y) +
    ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta m r

theorem rsC2Right_integrable {s : ℂ} {eta : ℝ} {m : ℕ} (hm : 0 < m)
    (hs : s.re ≤ 1) (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n) :
    IntegrableOn (rsC2RightIntegrand s eta m) (Ioi (-eta / 2)) := by
  have hc : ContinuousOn (fun y : ℝ =>
      rsHankelKernel s m ((eta : ℂ) + y * rsDescentDirection)) (Ici (-eta / 2)) := by
    intro y hy
    have h := (rsC2Right_kernel_analytic s he hint hy m).continuousAt.comp
      (show ContinuousAt (rsDescentPoint eta) y by unfold rsDescentPoint; fun_prop)
    simpa only [Function.comp_def, rsDescentPoint, mul_comm] using h.continuousWithinAt
  have hv : rsDescentDirection.im < 0 := by
    simp only [rsDescentDirection, div_ofReal_im, sub_im, one_im, I_im, zero_sub]
    exact div_neg_of_neg_of_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have h := (rsHankel_affine_tail_integrable hm hs hv (-eta / 2) hc).const_mul rsDescentDirection
  change Integrable (fun y : ℝ => rsDescentDirection *
    rsHankelKernel s m ((eta : ℂ) + y * rsDescentDirection)) _ at h
  have hf : (fun y : ℝ => rsDescentDirection *
      rsHankelKernel s m ((eta : ℂ) + y * rsDescentDirection)) =
      rsC2RightIntegrand s eta m := by
    funext y
    simp only [rsC2RightIntegrand, rsDescentPoint, mul_comm]
  rw [hf] at h
  exact h

theorem rsC2Left_integrable {s : ℂ} {eta : ℝ} {m : ℕ} (hm : 0 < m)
    (hs : s.re ≤ 1) (he : 0 < eta) :
    IntegrableOn (rsC2LeftIntegrand s eta m) (Ioi 0) := by
  have hc : Continuous (fun r : ℝ => rsHankelKernel s m (rsC2LeftPoint eta m r)) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (rsC2Left_kernel_analytic s he m r).continuousAt.comp
      (by unfold rsC2LeftPoint; fun_prop)
  have hv : (rsC2LeftDirection eta m).im < 0 := by
    have hh := (rsC2Corner_upper he).2
    simpa [rsC2LeftDirection] using hh
  exact (rsHankel_affine_tail_integrable hm hs hv 0 hc.continuousOn).const_mul _

theorem rsSourceC2_truncation_limit {s : ℂ} {eta : ℝ} {m : ℕ} (hm : 0 < m)
    (hs : s.re ≤ 1) (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n) :
    Tendsto (fun T : ℝ =>
      -(∫ y : ℝ in (-eta / 2)..T, rsC2RightIntegrand s eta m y) +
        ∫ r : ℝ in 0..T, rsC2LeftIntegrand s eta m r)
      atTop (𝓝 (rsSourceC2 s eta m)) := by
  exact (intervalIntegral_tendsto_integral_Ioi (-eta / 2)
    (rsC2Right_integrable hm hs he hint) tendsto_id).neg.add
      (intervalIntegral_tendsto_integral_Ioi 0 (rsC2Left_integrable hm hs he) tendsto_id)

theorem rsSourceC2_local_split {s : ℂ} {eta : ℝ} {m : ℕ} (hm : 0 < m)
    (hs : s.re ≤ 1) (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n) :
    rsSourceC2 s eta m =
      (∫ y : ℝ in (eta / 2)..(-eta / 2), rsC2RightIntegrand s eta m y) +
      (∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta m r) -
        ∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta m y := by
  have hi := rsC2Right_integrable hm hs he hint
  have hi' := hi.mono_set (show Ioi (eta / 2) ⊆ Ioi (-eta / 2) by
    intro y hy; simp only [mem_Ioi] at hy ⊢; linarith)
  have h := intervalIntegral.integral_Ioi_sub_Ioi' hi hi'
  rw [intervalIntegral.integral_symm] at h
  unfold rsSourceC2
  linear_combination -h

theorem rsSourceC2_local_truncation (sigma : ℝ) {eta : ℝ} {m : ℕ} (N : ℕ)
    (hm : 0 < m) (hs : sigma ≤ 1) (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n) :
    rsSourceC2 ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m =
      rsLocalPrefactor sigma eta m *
        ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsLocalPolynomialIntegrand sigma eta m N y) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m N y) +
      (∫ r : ℝ in Ioi 0, rsC2LeftIntegrand
        ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m r) -
      ∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand
        ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m y := by
  have hs' : (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) : ℂ).re ≤ 1 := by
    simpa only [add_re, mul_re, ofReal_re, ofReal_im, pow_two, mul_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add] using hs
  rw [rsSourceC2_local_split hm hs' he hint]
  change (∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) m
      (rsDescentPoint eta y)) + _ - _ = _
  rw [rsHankel_local_truncation sigma m N he hint]

end LiuWang.Proof.Campaign20260915.ZetaValidation
