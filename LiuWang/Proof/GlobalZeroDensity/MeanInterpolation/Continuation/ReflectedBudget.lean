import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ReflectedDetector
import LiuWang.Proof.GlobalZeroDensity.Strip.Window

set_option autoImplicit false

noncomputable section

open Complex Set Metric
open scoped ComplexConjugate
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def windowMajorant (y ξ : ℝ) : ℝ :=
  42 * y ^ (4 * (1 - ξ)) * Real.log y ^ (8 * ξ - 4) +
    (169 / 100) * Real.log y ^ 4

theorem source_power_antitone {y ξ σ : ℝ} (hy : 10000 ≤ y) (hξσ : ξ ≤ σ) :
    y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4) ≤
      y ^ (4 * (1 - ξ)) * Real.log y ^ (8 * ξ - 4) := by
  have hL : 0 < Real.log y := lt_of_lt_of_le (by norm_num) (Sharp.log_ge_nine hy)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div (ne_of_gt hL) (by norm_num)] at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hhalf : 2 * Real.log (Real.log y) ≤ Real.log y := by linarith
  rw [Real.rpow_def_of_pos (by linarith : 0 < y), Real.rpow_def_of_pos hL,
    Real.rpow_def_of_pos (by linarith : 0 < y), Real.rpow_def_of_pos hL,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hξσ)
    (show 0 ≤ Real.log y - 2 * Real.log (Real.log y) by linarith)]

theorem windowMajorant_nonneg {y : ℝ} (hy : 10000 ≤ y) (ξ : ℝ) :
    0 ≤ windowMajorant y ξ := by
  have hy0 : 0 ≤ y := by linarith
  have hL : 0 ≤ Real.log y := le_trans (by norm_num) (Sharp.log_ge_nine hy)
  unfold windowMajorant
  positivity

theorem K_le_windowMajorant {y ξ σ : ℝ} (hy : 10000 ≤ y)
    (hξ : 1 / 2 ≤ ξ) (hξσ : ξ ≤ σ) :
    K y σ ≤ windowMajorant y ξ := by
  have hleft : 0 ≤ 42 * y ^ (4 * (1 - ξ)) * Real.log y ^ (8 * ξ - 4) := by
    have hy0 : 0 ≤ y := by linarith
    have hL : 0 ≤ Real.log y := le_trans (by norm_num) (Sharp.log_ge_nine hy)
    positivity
  have hright : 0 ≤ (169 / 100 : ℝ) * Real.log y ^ 4 := by positivity
  by_cases hσ : σ ≤ 1 + delta y
  · have hK := K_left hy ⟨le_trans hξ hξσ, hσ⟩
    have hpow := mul_le_mul_of_nonneg_left (source_power_antitone hy hξσ)
      (by norm_num : (0 : ℝ) ≤ 42)
    unfold windowMajorant
    nlinarith
  · have hK := K_right hy (lt_of_not_ge hσ).le
    unfold windowMajorant
    linarith

theorem norm_H_le_one_add_F (y : ℝ) (s : ℂ) : ‖H y s‖ ≤ 1 + F y s := by
  calc
    ‖H y s‖ ≤ ‖(1 : ℂ)‖ + ‖f y s ^ 2‖ := norm_sub_le _ _
    _ = 1 + F y s := by rw [norm_one, norm_pow]; rfl

theorem norm_H_window {y ξ : ℝ} (hy : 10000 ≤ y) (hξ : 1 / 2 ≤ ξ)
    {s : ℂ} (hre : ξ ≤ s.re) (him : |s.im - y| ≤ 3 / 2) :
    ‖H y s‖ ≤ 1 + windowMajorant y ξ := by
  obtain ⟨_, _, _, hK⟩ := K_attained hy s.re
  have ht : s.im ∈ Icc (y - 3 / 2) (y + 3 / 2) := by
    constructor <;> linarith [abs_le.mp him]
  have hs : ((s.re : ℂ) + s.im * I) = s := Complex.re_add_im s
  have hb := hK s.im ht
  rw [hs] at hb
  exact (norm_H_le_one_add_F y s).trans
    (add_le_add (le_refl 1) (hb.trans (K_le_windowMajorant hy hξ hre)))

theorem reflectedH_disk_bound {y U R : ℝ} (hy : 10000 ≤ y)
    (hR : R ≤ 3 / 2) (hwin : |U - y| + R ≤ 3 / 2)
    {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) R) :
    ‖reflectedH y U s‖ ≤ 2 * (1 + windowMajorant y (2 - R)) := by
  have hn := mem_closedBall_iff_norm.mp hs
  have hre : 2 - R ≤ s.re := by
    have h : |s.re - 2| ≤ R := by
      simpa using (Complex.abs_re_le_norm (s - 2)).trans hn
    linarith [abs_le.mp h]
  have him : |s.im| ≤ R := by
    have h := (Complex.abs_im_le_norm (s - 2)).trans hn
    simpa using h
  have hp : |(s + U * I).im - y| ≤ 3 / 2 := by
    simp only [add_im, mul_I_im, ofReal_re]
    calc
      |s.im + U - y| = |s.im + (U - y)| := by congr 1; ring
      _ ≤ |s.im| + |U - y| := abs_add_le _ _
      _ ≤ 3 / 2 := by linarith
  have hm : |(conj (s - U * I)).im - y| ≤ 3 / 2 := by
    simp only [conj_im, sub_im, mul_I_im, ofReal_re]
    calc
      |-(s.im - U) - y| = |-s.im + (U - y)| := by congr 1; ring
      _ ≤ |-s.im| + |U - y| := abs_add_le _ _
      _ ≤ 3 / 2 := by rw [abs_neg]; linarith
  have hξ : (1 : ℝ) / 2 ≤ 2 - R := by linarith
  have hplus := norm_H_window hy hξ (s := s + U * I) (by simpa using hre) hp
  have hminus := norm_H_window hy hξ (s := conj (s - U * I)) (by simpa using hre) hm
  rw [H_conj, norm_conj] at hminus
  exact (norm_add_le _ _).trans (by linarith)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
