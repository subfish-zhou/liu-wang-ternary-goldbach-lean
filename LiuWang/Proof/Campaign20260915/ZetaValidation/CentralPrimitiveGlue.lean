import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelExpandedSource
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Complex.HasPrimitives

set_option autoImplicit false
noncomputable section
open Complex Set Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem central_exact_convex {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hc : Convex ℝ U) (hf : DifferentiableOn ℂ f U) :
    IsExactOn f U := by
  obtain ⟨g, hg⟩ := hc.exists_forall_hasDerivWithinAt hf
  exact ⟨g, fun z hz => (hg z hz).hasDerivAt (hU.mem_nhds hz)⟩

theorem central_exact_union {f : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hc : IsPreconnected (U ∩ V))
    (hne : (U ∩ V).Nonempty) (hfU : IsExactOn f U) (hfV : IsExactOn f V) :
    IsExactOn f (U ∪ V) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨g, hg⟩ := hfU
  obtain ⟨h, hh₀, hh⟩ := hfV.with_val_at z₀ (g z₀)
  have he : EqOn g h (U ∩ V) := (hU.inter hV).eqOn_of_deriv_eq hc
    (fun z hz => (hg z hz.1).differentiableAt.differentiableWithinAt)
    (fun z hz => (hh z hz.2).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hg z hz.1).deriv, (hh z hz.2).deriv]) hz₀ hh₀.symm
  refine ⟨U.piecewise g h, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · apply (hg z hz).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with w hw
    exact piecewise_eq_of_mem U g h hw
  · apply (hh z hz).congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hz] with w hw
    by_cases hwU : w ∈ U
    · rw [piecewise_eq_of_mem U g h hwU]
      exact he ⟨hwU, hw⟩
    · exact piecewise_eq_of_notMem U g h hwU

end LiuWang.Proof.Campaign20260915.ZetaValidation
