import LiuWang.Proof.ChebyshevBound.IntegratedFormula.MellinKernel
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # 用可积控制函数交换 Mellin 积分与可数级数。 -/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

theorem hasMellin_tsum_dominated {ι : Type*} [Countable ι]
    {f : ι → ℝ → ℂ} {a : ι → ℂ} {s : ℂ} {g : ℝ → ℂ} {w : ι → ℝ}
    (hf : ∀ i, HasMellin (f i) s (a i)) (hg : MellinConvergent g s)
    (hw : Summable w)
    (hbound : ∀ i u, 0 < u → ‖f i u‖ ≤ w i * ‖g u‖) :
    HasMellin (fun u => ∑' i, f i u) s (∑' i, a i) := by
  let F := fun i (u : ℝ) => (u : ℂ) ^ (s - 1) * f i u
  let G := fun u : ℝ => ‖(u : ℂ) ^ (s - 1) * g u‖
  have hF (i : ι) : IntegrableOn (F i) (Ioi 0) := (hf i).1
  have hG : IntegrableOn G (Ioi 0) := hg.norm
  have hb (i : ι) (u : ℝ) (hu : 0 < u) : ‖F i u‖ ≤ w i * G u := by
    dsimp [F, G]
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖(u : ℂ) ^ (s - 1)‖ * (w i * ‖g u‖) :=
        mul_le_mul_of_nonneg_left (hbound i u hu) (norm_nonneg _)
      _ = _ := by ring
  have hfs (u : ℝ) (hu : 0 < u) : Summable (fun i => f i u) :=
    (hw.mul_right ‖g u‖).of_norm_bounded (fun i => hbound i u hu)
  have hFs (u : ℝ) (hu : 0 < u) : Summable (fun i => F i u) :=
    (hfs u hu).mul_left _
  have hlim : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      HasSum (fun i => F i u) ((u : ℂ) ^ (s - 1) * ∑' i, f i u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hfs u hu).hasSum.mul_left _
  have hmajor : IntegrableOn (fun u => ∑' i, w i * G u) (Ioi 0) := by
    simp_rw [tsum_mul_right]
    exact hG.const_mul _
  have hi := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (fun i u => w i * G u) (fun i => (hF i).aestronglyMeasurable)
    (fun i => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hb i u hu)
    (by filter_upwards with u; exact hw.mul_right _)
    hmajor hlim
  have hmeas : AEStronglyMeasurable (fun u => ∑' i, F i u) (volume.restrict (Ioi 0)) :=
    (AEMeasurable.tsum (fun i => (hF i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hint : IntegrableOn (fun u => ∑' i, F i u) (Ioi 0) := by
    apply hmajor.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (norm_tsum_le_tsum_norm (hFs u hu).norm).trans
      ((hFs u hu).norm.tsum_le_tsum (fun i => hb i u hu) (hw.mul_right _))
  have heq : (fun u : ℝ => (u : ℂ) ^ (s - 1) * ∑' i, f i u) = fun u => ∑' i, F i u := by
    funext u
    exact (tsum_mul_left).symm
  refine ⟨?_, ?_⟩
  · change IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * ∑' i, f i u) (Ioi 0)
    rwa [heq]
  · have hia : (fun i => ∫ u in Ioi 0, F i u) = a := by
      funext i
      exact (hf i).2
    rw [hia] at hi
    exact hi.tsum_eq.symm

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
