import LiuWang.Proof.ChebyshevBound.IntegratedFormula.SpectralMellin
import Mathlib.Analysis.Normed.Group.Tannery

/-! # 反演所需的实际级数连续性；在正端点局部统一绝对控制。 -/

set_option autoImplicit false
noncomputable section

open Complex Set Filter ArithmeticFunction
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

theorem continuousAt_powerCut (a : ℂ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ContinuousAt (powerCut a) u := by
  apply (Complex.continuousAt_ofReal_cpow_const u a (Or.inr hu.ne')).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hu1] with v hv hv1
  exact indicator_of_mem (show v ∈ Ioc 0 1 from ⟨hv, hv1.le⟩) _

theorem continuousAt_tsum_with_envelope {ι : Type*} {f : ι → ℝ → ℂ}
    {w : ι → ℝ} {g : ℝ → ℂ} {u : ℝ} (hu : 0 < u)
    (hf : ∀ i, ContinuousAt (f i) u) (hg : ContinuousAt g u)
    (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i)
    (hbound : ∀ i v, 0 < v → ‖f i v‖ ≤ w i * ‖g v‖) :
    ContinuousAt (fun v => ∑' i, f i v) u := by
  apply tendsto_tsum_of_dominated_convergence (hw.mul_right (‖g u‖ + 1)) hf
  filter_upwards [eventually_gt_nhds hu,
    hg.norm.eventually (eventually_lt_nhds (show ‖g u‖ < ‖g u‖ + 1 by linarith))] with v hv hgv
  intro i
  exact (hbound i v hv).trans (mul_le_mul_of_nonneg_left hgv.le (hw0 i))

theorem continuousAt_mangoldtSum {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ContinuousAt (fun v => ∑' n, mangoldtTriangle n v) u := by
  apply continuousAt_tsum_with_envelope hu _ (continuousAt_powerCut (-2) hu hu1)
    (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    (fun _ => norm_nonneg _) (fun n _ hv => mangoldtTriangle_norm_le n hv)
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [mangoldtTriangle] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) u)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact continuousAt_const.mul ((continuousAt_triangle (mul_pos hn0 hu)).comp
    (by fun_prop))

theorem continuousAt_zeroSum {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ContinuousAt (fun v => ∑' p, zeroMellinTerm p v) u := by
  apply continuousAt_tsum_with_envelope hu _ (continuousAt_powerCut (-1) hu hu1)
    (xi_height_inverse_square_summable.mul_left 2) (fun _ => by positivity)
    (fun p _ hv => zeroMellinTerm_norm_le p hv)
  intro p
  exact ((continuousAt_powerCut _ hu hu1).sub (continuousAt_powerCut _ hu hu1)).div_const _

theorem continuousAt_gammaSum {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ContinuousAt (fun v => ∑' n, gammaMellinTerm n v) u := by
  apply continuousAt_tsum_with_envelope hu _ (continuousAt_powerCut 0 hu hu1)
    gammaMellin_weights_summable (fun _ => by positivity)
    (fun n _ hv => gammaMellinTerm_norm_le n hv)
  intro n
  exact ((continuousAt_powerCut _ hu hu1).sub (continuousAt_powerCut _ hu hu1)).div_const _

theorem continuousAt_spectralMellin {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ContinuousAt spectralMellin u := by
  have hp : ContinuousAt poleMellin u :=
    (((continuousAt_powerCut _ hu hu1).sub
      (continuousAt_const.mul (continuousAt_powerCut _ hu hu1))).add
      (continuousAt_powerCut _ hu hu1)).div_const _
  exact (((continuousAt_const.mul (continuousAt_triangle hu)).sub
    (continuousAt_zeroSum hu hu1)).add hp).add (continuousAt_gammaSum hu hu1)

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
