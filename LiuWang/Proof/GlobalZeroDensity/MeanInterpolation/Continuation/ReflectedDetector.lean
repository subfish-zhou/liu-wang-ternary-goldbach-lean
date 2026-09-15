import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.Consumer
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.JensenFormula

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory Metric
open scoped ComplexConjugate

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def reflectedH (y U : ℝ) (s : ℂ) : ℂ :=
  H y (s + U * I) + H y (s - U * I)

theorem Q_conj (y : ℝ) (s : ℂ) : Q y (conj s) = conj (Q y s) := by
  unfold Q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.cpow_conj _ _ (by simpa using Real.pi_pos.ne)]
  simp

theorem H_conj (y : ℝ) (s : ℂ) : H y (conj s) = conj (H y s) := by
  simp [H, f, Q_conj, riemannZeta_conj]

theorem reflectedH_real (y U x : ℝ) :
    reflectedH y U x = (2 * (H y ((x : ℂ) + U * I)).re : ℝ) := by
  have hc : (x : ℂ) - U * I = conj ((x : ℂ) + U * I) := by simp [sub_eq_add_neg]
  rw [reflectedH, hc, H_conj]
  exact Complex.add_conj _

theorem H_re_two_lower {y : ℝ} (hy : 1 < y) (t : ℝ) :
    1 - 4 / (y - 1) ^ 2 ≤ (H y ((2 : ℂ) + t * I)).re := by
  have hn := norm_f_two_le (by simp : (((2 : ℂ) + t * I)).re = 2) hy
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hr := Complex.re_le_norm (f y ((2 : ℂ) + t * I) ^ 2)
  rw [norm_pow] at hr
  have he : (2 / (y - 1)) ^ 2 = 4 / (y - 1) ^ 2 := by rw [div_pow]; norm_num
  rw [he] at hs
  simp only [H, sub_re, one_re]
  linarith

theorem reflectedH_two_lower {y : ℝ} (hy : 1 < y) (U : ℝ) :
    2 - 8 / (y - 1) ^ 2 ≤ (reflectedH y U 2).re := by
  have h := H_re_two_lower hy U
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, reflectedH_real]
  simp only [ofReal_re, ofReal_ofNat]
  rw [show 2 - 8 / (y - 1) ^ 2 = 2 * (1 - 4 / (y - 1) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem reflectedH_two_ne_zero {y : ℝ} (hy : 5 ≤ y) (U : ℝ) :
    reflectedH y U 2 ≠ 0 := by
  have h := reflectedH_two_lower (by linarith : 1 < y) U
  have hq : 8 / (y - 1) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < y - 1))).mpr
    nlinarith
  intro hz
  rw [hz, zero_re] at h
  linarith

theorem shifted_ne_one {U R : ℝ} (hUR : R < U) {s : ℂ}
    (hs : s ∈ closedBall (2 : ℂ) R) :
    s + U * I ≠ 1 ∧ s - U * I ≠ 1 := by
  have hi : |s.im| ≤ R := by
    have h := (Complex.abs_im_le_norm (s - 2)).trans (mem_closedBall_iff_norm.mp hs)
    simpa using h
  constructor <;> intro h <;> have hh := congrArg Complex.im h
  · simp only [add_im, mul_I_im, ofReal_re, one_im] at hh
    linarith [abs_le.mp hi]
  · simp only [sub_im, mul_I_im, ofReal_re, one_im] at hh
    linarith [abs_le.mp hi]

theorem analytic_H_at (y : ℝ) {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (H y) s :=
  analyticAt_const.sub ((((analytic_zeta s hs).mul
    ((differentiable_Q y).analyticAt s)).sub analyticAt_const).pow 2)

theorem reflectedH_analytic {y U R : ℝ} (hUR : R < U) :
    AnalyticOnNhd ℂ (reflectedH y U) (closedBall (2 : ℂ) R) := by
  intro s hs
  obtain ⟨hp, hm⟩ := shifted_ne_one hUR hs
  exact ((analytic_H_at y hp).comp (f := fun z : ℂ => z + U * I)
    (analyticAt_id.add analyticAt_const)).add
    ((analytic_H_at y hm).comp (f := fun z : ℂ => z - U * I)
      (analyticAt_id.sub analyticAt_const))

theorem reflectedH_real_zero_iff (y U x : ℝ) :
    reflectedH y U x = 0 ↔ (H y ((x : ℂ) + U * I)).re = 0 := by
  rw [reflectedH_real, ofReal_eq_zero]
  simp

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
