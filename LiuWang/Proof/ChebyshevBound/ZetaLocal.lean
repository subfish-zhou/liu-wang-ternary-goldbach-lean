import LiuWang.Proof.ChebyshevBound.ZetaAbel
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# ζ 极点附近的显式对数导数界

Abel 余因子在半径 1/2 的闭圆盘上受控，Cauchy 估计给出
半径 1/4 内的导数界。常数 8 不含未定渐近常数。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace LiuWang.Proof.ChebyshevBound

def abelPoleFactor (s : ℂ) : ℂ :=
  1 - (s - 1) * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u

theorem analyticAt_abelPoleFactor {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ abelPoleFactor s :=
  analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul
    (ZetaAbelFractKernel.integral_analytic s hs))

theorem re_lower_of_norm_sub_one_le {s : ℂ} {r : ℝ} (hs : ‖s - 1‖ ≤ r) :
    1 - r ≤ s.re := by
  have h := Complex.re_le_norm (1 - s)
  rw [norm_sub_rev] at h
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

theorem norm_abelPoleFactor_sub_one_le_one {s : ℂ} (hs : ‖s - 1‖ ≤ 1 / 2) :
    ‖abelPoleFactor s - 1‖ ≤ 1 := by
  have hre := re_lower_of_norm_sub_one_le hs
  have hs0 : 0 < s.re := by linarith
  exact (norm_zeta_pole_factor_sub_one_le hs0).trans
    ((div_le_one hs0).2 (by linarith))

theorem two_thirds_le_norm_abelPoleFactor {s : ℂ} (hs : ‖s - 1‖ ≤ 1 / 4) :
    2 / 3 ≤ ‖abelPoleFactor s‖ := by
  have hre := re_lower_of_norm_sub_one_le hs
  have hs0 : 0 < s.re := by linarith
  have hsmall : ‖abelPoleFactor s - 1‖ ≤ 1 / 3 :=
    (norm_zeta_pole_factor_sub_one_le hs0).trans
      ((div_le_iff₀ hs0).2 (by linarith))
  have h := norm_sub_norm_le (1 : ℂ) (abelPoleFactor s)
  rw [norm_one, norm_sub_rev] at h
  linarith

theorem norm_deriv_abelPoleFactor_le_four {s : ℂ} (hs : ‖s - 1‖ ≤ 1 / 4) :
    ‖deriv abelPoleFactor s‖ ≤ 4 := by
  have hball {z : ℂ} (hz : z ∈ closedBall s (1 / 4)) : ‖z - 1‖ ≤ 1 / 2 := by
    have hz' := mem_closedBall_iff_norm.mp hz
    calc
      ‖z - 1‖ ≤ ‖z - s‖ + ‖s - 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 / 2 := by linarith
  have hd : DifferentiableOn ℂ (fun z => abelPoleFactor z - 1)
      (closure (ball s (1 / 4))) := by
    rw [closure_ball s (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    intro z hz
    exact ((analyticAt_abelPoleFactor
      (by linarith [re_lower_of_norm_sub_one_le (hball hz)])).differentiableAt.sub_const
        1).differentiableWithinAt
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) hd.diffContOnCl
    (fun z hz => norm_abelPoleFactor_sub_one_le_one
      (hball (sphere_subset_closedBall hz)))
  norm_num only [deriv_sub_const, one_div, inv_inv] at hc
  exact hc

theorem norm_logDeriv_abelPoleFactor_le_six {s : ℂ} (hs : ‖s - 1‖ ≤ 1 / 4) :
    ‖logDeriv abelPoleFactor s‖ ≤ 6 := by
  rw [logDeriv_apply, norm_div]
  have hl := two_thirds_le_norm_abelPoleFactor hs
  apply (div_le_iff₀ (by linarith : 0 < ‖abelPoleFactor s‖)).2
  linarith [norm_deriv_abelPoleFactor_le_four hs]

theorem logDeriv_riemannZeta_add_pole_eq {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / 4) (hs1 : s ≠ 1) :
    logDeriv riemannZeta s + 1 / (s - 1) =
      1 / s + logDeriv abelPoleFactor s := by
  have hre := re_lower_of_norm_sub_one_le hs
  have hs0 : 0 < s.re := by linarith
  have hsn : s ≠ 0 := by
    intro h
    simp [h] at hs0
  have hf : abelPoleFactor s ≠ 0 := by
    have h := two_thirds_le_norm_abelPoleFactor hs
    intro hz
    norm_num [hz] at h
  have heq : riemannZeta =ᶠ[𝓝 s] fun z => z / (z - 1) * abelPoleFactor z := by
    filter_upwards [(isOpen_zetaAbelContinuationDomain.mem_nhds
      (show s ∈ zetaAbelContinuationDomain from ⟨hs1, by
        change 1 / 10 < s.re
        linarith⟩))] with z hz
    exact zeta_eq_pole_mul_abel hz.2 hz.1
  have hlog : logDeriv riemannZeta s =
      logDeriv (fun z => z / (z - 1) * abelPoleFactor z) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.self_of_nhds]
  rw [hlog, logDeriv_mul (f := fun z : ℂ => z / (z - 1)) (g := abelPoleFactor)
    s (div_ne_zero hsn (sub_ne_zero.mpr hs1)) hf
    ((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).div
      (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
    (analyticAt_abelPoleFactor hs0).differentiableAt,
    logDeriv_div (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
      s hsn (sub_ne_zero.mpr hs1) differentiableAt_id
      (differentiableAt_id.sub_const 1)]
  simp [logDeriv_apply]
  ring

theorem norm_logDeriv_riemannZeta_add_pole_le_eight {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / 4) (hs1 : s ≠ 1) :
    ‖logDeriv riemannZeta s + 1 / (s - 1)‖ ≤ 8 := by
  have hre := re_lower_of_norm_sub_one_le hs
  have hsNorm : 3 / 4 ≤ ‖s‖ := by linarith [Complex.re_le_norm s]
  have hinv : ‖1 / s‖ ≤ 4 / 3 := by
    rw [norm_div, norm_one]
    exact (div_le_iff₀ (by linarith : 0 < ‖s‖)).2 (by linarith)
  rw [logDeriv_riemannZeta_add_pole_eq hs hs1]
  exact (norm_add_le _ _).trans (by linarith [norm_logDeriv_abelPoleFactor_le_six hs])

theorem norm_logDeriv_riemannZeta_real_le {b : ℝ} (hb : 1 < b) (hb' : b ≤ 5 / 4) :
    ‖logDeriv riemannZeta (b : ℂ)‖ ≤ 1 / (b - 1) + 8 := by
  have hdisk : ‖(b : ℂ) - 1‖ ≤ 1 / 4 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < b - 1)]
    linarith
  have hb1 : (b : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  have h := norm_logDeriv_riemannZeta_add_pole_le_eight hdisk hb1
  have hpole : ‖1 / ((b : ℂ) - 1)‖ = 1 / (b - 1) := by
    rw [norm_div, norm_one, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < b - 1)]
  calc
    _ = ‖(logDeriv riemannZeta (b : ℂ) + 1 / ((b : ℂ) - 1)) -
        1 / ((b : ℂ) - 1)‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖logDeriv riemannZeta (b : ℂ) + 1 / ((b : ℂ) - 1)‖ +
        ‖1 / ((b : ℂ) - 1)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [hpole]
      linarith

end LiuWang.Proof.ChebyshevBound
