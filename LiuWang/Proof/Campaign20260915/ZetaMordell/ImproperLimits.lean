import LiuWang.Proof.Campaign20260915.ZetaMordell.CorrectionIntegral

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

theorem mordellIntegral_tendsto (a : ℂ) :
    Tendsto (fun T : ℝ => ∫ t in -T..T, mordellKernel a t)
      atTop (𝓝 (mordellIntegral a)) :=
  intervalIntegral_tendsto_integral (mordellKernel_integrable a)
    tendsto_neg_atTop_atBot tendsto_id

theorem siegelIntegral_tendsto (u : ℂ) :
    Tendsto (fun T : ℝ => ∫ t in -T..T, siegelKernel u t)
      atTop (𝓝 (siegelIntegral u)) :=
  intervalIntegral_tendsto_integral (siegelKernel_integrable u)
    tendsto_neg_atTop_atBot tendsto_id

theorem correctionIntegral_tendsto (z : ℂ) :
    Tendsto (fun T : ℝ => ∫ t in -T..T, correctionKernel z t)
      atTop (𝓝 (correctionIntegral z)) :=
  intervalIntegral_tendsto_integral (correctionKernel_integrable z)
    tendsto_neg_atTop_atBot tendsto_id

theorem correctionCenteredMoment_tendsto (n : ℕ) (z : ℂ) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,
      (siegelLine t - (z + 1) / 2) ^ n * correctionKernel z t)
      atTop (𝓝 (∫ t : ℝ, (siegelLine t - (z + 1) / 2) ^ n * correctionKernel z t)) :=
  intervalIntegral_tendsto_integral (correctionCenteredKernel_integrable n z)
    tendsto_neg_atTop_atBot tendsto_id

end LiuWang.Proof.Campaign20260915.ZetaMordell
