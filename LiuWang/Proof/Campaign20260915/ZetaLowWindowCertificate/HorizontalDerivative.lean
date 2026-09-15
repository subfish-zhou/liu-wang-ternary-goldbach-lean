import LiuWang.Proof.Campaign20260915.ZetaValidation.AbelEvaluation
import LiuWang.Proof.Campaign20260915.ZetaWinding.HorizontalCount
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
noncomputable section
open Complex Metric Set

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem quarter_strip_zeta_norm {s : ℂ}
    (hs : 1 / 4 ≤ s.re) (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ 2 * ‖s‖ + 1 := by
  have hs1 : s ≠ 1 := by
    intro he
    norm_num [he] at ht
  have hdist : 2 ≤ ‖s - 1‖ := by
    have h := im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero] at h
    exact ht.trans h
  have hinv : ‖1 / (s - 1)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have ha : abelApprox s 1 = (1 / 2 : ℂ) + 1 / (s - 1) := by
    norm_num [abelApprox, zetaPartialSum]
    ring
  have han : ‖abelApprox s 1‖ ≤ 1 := by
    rw [ha]
    calc
      _ ≤ ‖(1 / 2 : ℂ)‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add (by norm_num) hinv
      _ = _ := by norm_num
  have he := norm_zeta_sub_abelApprox_le (s := s)
    (by linarith) hs1 (N := 1) (by norm_num)
  norm_num at he
  have hb : ‖s‖ / (2 * s.re) ≤ 2 * ‖s‖ := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * s.re)).mpr
    nlinarith [norm_nonneg s]
  have h := norm_le_norm_add_norm_sub (abelApprox s 1) (riemannZeta s)
  rw [norm_sub_rev] at h
  linarith

theorem horizontal_quarter_disk_bounds {H x : ℝ} (hH : 16 ≤ H)
    (hxlo : 1 / 2 ≤ x) (hxhi : x ≤ 2) {z : ℂ}
    (hz : z ∈ closedBall (horizontalAt H x) (1 / 4)) :
    1 / 4 ≤ z.re ∧ 2 ≤ z.im ∧ ‖z‖ ≤ H + 5 / 2 := by
  have hn := mem_closedBall_iff_norm.mp hz
  have hr := abs_re_le_norm (z - horizontalAt H x)
  have hi := abs_im_le_norm (z - horizontalAt H x)
  simp only [sub_re, sub_im, horizontalAt, add_re, add_im, ofReal_re, ofReal_im,
    mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hr hi
  have hre := abs_le.mp (hr.trans hn)
  have him := abs_le.mp (hi.trans hn)
  have hzre : 1 / 4 ≤ z.re := by linarith [hre.1]
  have hzim : 2 ≤ z.im := by linarith [him.1]
  refine ⟨hzre, hzim, ?_⟩
  have hb := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg (by linarith : 0 ≤ z.re),
    abs_of_nonneg (by linarith : 0 ≤ z.im)] at hb
  linarith [hre.2, him.2]

theorem horizontal_derivative_bound {H x : ℝ} (hH : 16 ≤ H)
    (hxlo : 1 / 2 ≤ x) (hxhi : x ≤ 2) :
    ‖deriv riemannZeta (horizontalAt H x)‖ ≤ 8 * H + 24 := by
  have hd : DifferentiableOn ℂ riemannZeta
      (closure (ball (horizontalAt H x) (1 / 4))) := by
    rw [closure_ball _ (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    intro z hz
    have hb := horizontal_quarter_disk_bounds hH hxlo hxhi hz
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro he
    norm_num [he] at hb
  have hc : ∀ z ∈ sphere (horizontalAt H x) (1 / 4),
      ‖riemannZeta z‖ ≤ 2 * H + 6 := by
    intro z hz
    have hb := horizontal_quarter_disk_bounds hH hxlo hxhi
      (sphere_subset_closedBall hz)
    exact (quarter_strip_zeta_norm hb.1 hb.2.1).trans (by linarith [hb.2.2])
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) hd.diffContOnCl hc
  convert h using 1
  ring

theorem horizontal_cell_derivative_bound {H a b : ℝ} (hH : 16 ≤ H)
    (ha : 1 / 2 ≤ a) (hb : b ≤ 2) :
    ∀ t ∈ Icc a b, ‖deriv riemannZeta (horizontalAt H t)‖ ≤ 8 * H + 24 := by
  intro t ht
  exact horizontal_derivative_bound hH (ha.trans ht.1) (ht.2.trans hb)

theorem low_horizontal_derivative_bound {H x : ℝ}
    (hHlo : 16 ≤ H) (hHhi : H ≤ 12600) (hxlo : 1 / 2 ≤ x) (hxhi : x ≤ 2) :
    ‖deriv riemannZeta (horizontalAt H x)‖ ≤ 100824 :=
  (horizontal_derivative_bound hHlo hxlo hxhi).trans (by linarith)

theorem horizontal_ball_of_actual_derivative {H a b e : ℝ} {z : ℂ}
    (hH : 16 ≤ H) (ha : 1 / 2 ≤ a) (hb : b ≤ 2)
    (he : ‖riemannZeta (horizontalAt H a) - z‖ ≤ e) :
    ∀ t ∈ Icc a b,
      ‖riemannZeta (horizontalAt H t) - z‖ ≤ e + (8 * H + 24) * (b - a) :=
  horizontal_ball_of_endpoint_deriv (by linarith) (by linarith) he
    (horizontal_cell_derivative_bound hH ha hb)

#print axioms horizontal_derivative_bound
#print axioms horizontal_cell_derivative_bound
#print axioms low_horizontal_derivative_bound
#print axioms horizontal_ball_of_actual_derivative

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
