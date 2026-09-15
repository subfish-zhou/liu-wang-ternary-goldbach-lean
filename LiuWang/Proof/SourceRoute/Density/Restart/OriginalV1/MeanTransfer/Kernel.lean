import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

def sourceKernel (u : ℝ) : ℝ := Real.exp u / (2 + Real.exp u) ^ 2

theorem sourceKernel_pos (u : ℝ) : 0 < sourceKernel u := by
  unfold sourceKernel; positivity

theorem sourceKernel_continuous : Continuous sourceKernel := by
  unfold sourceKernel
  exact Real.continuous_exp.div
    ((continuous_const.add Real.continuous_exp).pow 2) (fun x => by positivity)

theorem sourceKernel_primitive (u : ℝ) :
    HasDerivAt (fun x : ℝ => -(2 + Real.exp x)⁻¹) (sourceKernel u) u := by
  convert! (((Real.hasDerivAt_exp u).const_add 2).inv (by positivity)).neg using 1
  unfold sourceKernel; ring

theorem sourceKernel_primitive_limit :
    Tendsto (fun x : ℝ => -(2 + Real.exp x)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 2 + Real.exp x) atTop atTop :=
    tendsto_atTop_add_const_left _ _ Real.tendsto_exp_atTop
  simpa using (tendsto_inv_atTop_zero.comp h).neg

theorem sourceKernel_integrable_tail (a : ℝ) :
    IntegrableOn sourceKernel (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => sourceKernel_primitive x)
    (fun x _ => (sourceKernel_pos x).le) sourceKernel_primitive_limit

theorem sourceKernel_tail (a : ℝ) :
    (∫ u in Ioi a, sourceKernel u) = 1 / (2 + Real.exp a) := by
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := a) (fun x _ => sourceKernel_primitive x)
    (fun x _ => (sourceKernel_pos x).le) sourceKernel_primitive_limit

theorem sourceKernel_ltail (a : ℝ) :
    (∫⁻ u in Ici a, ENNReal.ofReal (sourceKernel u)) =
      ENNReal.ofReal (1 / (2 + Real.exp a)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (sourceKernel_integrable_tail a))
    (Filter.Eventually.of_forall (fun u => (sourceKernel_pos u).le)),
    integral_Ici_eq_integral_Ioi, sourceKernel_tail]

theorem sourceKernel_window_identity {v : ℝ → ℝ} (hv : Measurable v)
    (y : ℝ) (hy : 0 < y) :
    (∫⁻ t : ℝ, ENNReal.ofReal (v t) *
      ENNReal.ofReal (1 / (2 + Real.exp (|t| / y)))) =
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (sourceKernel u) *
      ∫⁻ t in Icc (-(y * u)) (y * u), ENNReal.ofReal (v t) := by
  let K (p : ℝ × ℝ) : ℝ≥0∞ :=
    {p : ℝ × ℝ | |p.2| / y ≤ p.1}.indicator
      (fun p => ENNReal.ofReal (sourceKernel p.1) * ENNReal.ofReal (v p.2)) p
  have hkm : Measurable K := by
    apply Measurable.indicator
    · exact (sourceKernel_continuous.measurable.comp measurable_fst).ennreal_ofReal.mul
        (hv.comp measurable_snd).ennreal_ofReal
    · exact measurableSet_le
        (show Measurable (fun p : ℝ × ℝ => |p.2| / y) from (by fun_prop)) measurable_fst
  have hinner (u : ℝ) :
      (∫⁻ t : ℝ, K (u, t)) =
      ENNReal.ofReal (sourceKernel u) *
        ∫⁻ t in Icc (-(y * u)) (y * u), ENNReal.ofReal (v t) := by
    have he : (fun t => K (u, t)) =
        (Icc (-(y * u)) (y * u)).indicator
          (fun t => ENNReal.ofReal (sourceKernel u) * ENNReal.ofReal (v t)) := by
      funext t
      simp only [K, indicator_apply, mem_ofPred_eq, mem_Icc,
        div_le_iff₀ hy, abs_le, mul_comm y u]
    rw [he, lintegral_indicator measurableSet_Icc, lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  have houter (t : ℝ) :
      (∫⁻ u in Ioi (0 : ℝ), K (u, t)) =
      ENNReal.ofReal (v t) * ENNReal.ofReal (1 / (2 + Real.exp (|t| / y))) := by
    have he : (fun u => K (u, t)) =
        (Ici (|t| / y)).indicator
          (fun u => ENNReal.ofReal (sourceKernel u) * ENNReal.ofReal (v t)) := by
      rfl
    rw [he, restrict_Ioi_eq_restrict_Ici,
      setLIntegral_indicator measurableSet_Ici, Ici_inter_Ici,
      max_eq_left (div_nonneg (abs_nonneg t) hy.le), lintegral_mul_const']
    · rw [sourceKernel_ltail, mul_comm]
    · exact ENNReal.ofReal_ne_top
  have hswap := lintegral_lintegral_swap
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume)
    (f := fun u t => K (u, t)) hkm.aemeasurable
  simpa only [hinner, houter] using hswap.symm

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer
