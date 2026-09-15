import LiuWang.Proof.Campaign20260915.Totient.RSCountError
import LiuWang.Proof.Campaign20260915.Totient.RSDensityIntegral

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_theorem27_from_sharp_count {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2)
    {F E : ℝ → ℝ}
    (hderiv : ∀ t ∈ Ici K, HasDerivAt (fun u => F u + E u)
      (rsQ t * Real.log (t / (2 * Real.pi))) t)
    (hcount : ∀ t ∈ Ici K, |(positiveCount t : ℝ) - F t| ≤ E t) :
    (∑' p, rsPositivePhiTerm K m L p) <
      2 * E K * rsPhi m L K +
      rsQ K * ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
  have hD : ContinuousOn (fun t => rsQ t * Real.log (t / (2 * Real.pi))) (Ici K) := by
    apply (rsQ_continuousOn.mono (Ici_subset_Ici.mpr hK)).mul
    intro t ht
    have ht0 : 0 < t := by have h := hK.trans ht; linarith [rsA_ge_thousand]
    have hc : 2 * Real.pi ≠ 0 := by positivity
    have htc : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht0.ne' hc
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hI : IntegrableOn
      (fun t => (rsQ t * Real.log (t / (2 * Real.pi))) * rsPhi m L t) (Ioi K) := by
    convert rsQ_phi_density_integrableOn hK hL hm using 1
    ext t
    ring
  have hb := rs_positiveCount_two_remainders_infinite hK hL hm hupper hderiv hD hcount hI
  have he :
      (∫ t in Ioi K, (rsQ t * Real.log (t / (2 * Real.pi))) * rsPhi m L t) =
      ∫ t in Ioi K, rsQ t * (rsPhi m L t * Real.log (t / (2 * Real.pi))) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  rw [he] at hb
  exact hb.trans_lt (add_lt_add_of_le_of_lt le_rfl (rsQ_phi_density_strict hK hL hm))

#print axioms rs_theorem27_from_sharp_count

end LiuWang.Proof.Campaign20260915.Totient
