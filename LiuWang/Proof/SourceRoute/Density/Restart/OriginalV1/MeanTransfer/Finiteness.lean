import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.EulerIdentity
import LiuWang.Proof.GlobalZeroDensity.Strip.FullAxis

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

theorem F_measurable (y sigma : ℝ) :
    Measurable (fun t : ℝ => F y ((sigma : ℂ) + t * I)) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  intro t ht
  have hp : (sigma : ℂ) + t * I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact ht hi
  have hf : ContinuousAt (fun t : ℝ => f y ((sigma : ℂ) + t * I)) t :=
    (differentiableAt_f y hp).continuousAt.comp
      (f := fun t : ℝ => (sigma : ℂ) + t * I) (by fun_prop)
  exact (hf.norm.pow 2).continuousWithinAt

theorem F_polynomial_bound (y : ℝ) {sigma : ℝ} (hs : 0 < sigma) (hs1 : sigma ≠ 1) :
    ∃ a b : ℝ, ∀ t : ℝ, F y ((sigma : ℂ) + t * I) ≤ (a + b * |t|) ^ 2 := by
  let d := |sigma - 1|
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hs1)
  let a := (⌈y⌉₊ : ℝ) * ((|sigma| + 1) / (2 * d) + |sigma| / (2 * sigma)) + 1
  let b := (⌈y⌉₊ : ℝ) * (1 / (2 * d) + 1 / (2 * sigma))
  refine ⟨a, b, fun t => ?_⟩
  let s := (sigma : ℂ) + t * I
  have hp : s ≠ 1 := by intro h; have h' := congrArg Complex.re h; simp [s] at h'; exact hs1 h'
  have hr : s.re = sigma := by simp [s]
  have hz := Titchmarsh.zeta_norm_le_one_cutoff (by rwa [hr]) hp
  have hsn : ‖s‖ ≤ |sigma| + |t| := by
    simpa [s] using norm_add_le (sigma : ℂ) ((t : ℂ) * I)
  have hsp : ‖s + 1‖ ≤ |sigma| + |t| + 1 := by
    have h := norm_add_le s (1 : ℂ)
    norm_num at h; linarith
  have hsm : d ≤ ‖s - 1‖ := by
    simpa [s, d] using Complex.abs_re_le_norm (s - 1)
  have hq := Strip.norm_Q_strip_le (s := s) (by rw [hr]; exact hs.le) y
  have hz' : ‖riemannZeta s‖ ≤
      (|sigma| + |t| + 1) / (2 * d) + (|sigma| + |t|) / (2 * sigma) := by
    rw [hr] at hz
    apply hz.trans
    exact add_le_add
      (div_le_div₀ (by positivity) hsp (by positivity) (by linarith))
      (div_le_div_of_nonneg_right hsn (by positivity))
  have hmul := mul_le_mul hz' hq (norm_nonneg _) (by positivity)
  have hf := norm_sub_le (riemannZeta s * Q y s) 1
  rw [norm_mul, norm_one] at hf
  have hbound : ‖f y s‖ ≤ a + b * |t| := by
    dsimp [a, b, f]
    have he :
        ((|sigma| + |t| + 1) / (2 * d) + (|sigma| + |t|) / (2 * sigma)) *
          (⌈y⌉₊ : ℝ) + 1 =
        (⌈y⌉₊ : ℝ) * ((|sigma| + 1) / (2 * d) + |sigma| / (2 * sigma)) + 1 +
          (⌈y⌉₊ : ℝ) * (1 / (2 * d) + 1 / (2 * sigma)) * |t| := by ring
    linarith
  exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

theorem F_weighted_integrable {y sigma : ℝ} (hy : 0 < y)
    (hs : 0 < sigma) (hs1 : sigma ≠ 1) :
    Integrable (fun t : ℝ =>
      F y ((sigma : ℂ) + t * I) / (2 + Real.exp (|t| / y))) := by
  obtain ⟨a, b, hab⟩ := F_polynomial_bound y hs hs1
  have hc : Continuous (fun t : ℝ =>
      F y ((sigma : ℂ) + t * I) / (2 + Real.exp (|t| / y))) :=
    (continuous_vertical_F y hs1).div (by fun_prop) (fun t => by positivity)
  apply (Strip.polynomial_exponential_abs_integrable hy a b).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
  rw [Real.norm_of_nonneg (by unfold F; positivity)]
  calc
    _ ≤ (a + b * |t|) ^ 2 / (2 + Real.exp (|t| / y)) :=
      div_le_div_of_nonneg_right (hab t) (by positivity)
    _ ≤ (a + b * |t|) ^ 2 / Real.exp (|t| / y) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (Real.exp_pos _) (by linarith)
    _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg, neg_div]

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer
