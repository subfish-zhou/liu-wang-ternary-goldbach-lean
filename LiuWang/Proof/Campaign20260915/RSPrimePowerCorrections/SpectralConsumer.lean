import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.Main
import LiuWang.Proof.Campaign20260915.Totient.RSSpectralBounds

set_option autoImplicit false

noncomputable section

open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

theorem rsTheta_original_moment_bounds_raw {m : ℕ} (hm : 1 ≤ m)
    {δ a x : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x) :
    x - (m : ℝ) * δ * x / 2 -
        x * 2 ^ m / δ ^ m * (∑' p, rsZeroMoment m (Real.log x) p) -
        1.84 - Real.log 4 * Real.sqrt x - 3 * x ^ (1 / (3 : ℝ)) <
      Chebyshev.theta x ∧
    Chebyshev.theta x <
      x + (m : ℝ) * δ * x / 2 +
        x * (1 + (1 + δ) ^ (m + 1)) ^ m / δ ^ m *
          (∑' p, rsZeroMoment m (Real.log x) p) + rsTrivialKernel x := by
  obtain ⟨hL, hU⟩ := rsPsi_original_moment_bounds hm hδ ha hcut hax
  exact ⟨(theta_bounds_of_psi_bounds_raw (ha.trans_le hax) hL.le hU.le).1,
    (Chebyshev.theta_le_psi x).trans_lt hU⟩

#print axioms rsTheta_original_moment_bounds_raw

end LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections
