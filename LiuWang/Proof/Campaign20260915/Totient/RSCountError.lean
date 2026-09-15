import LiuWang.Proof.Campaign20260915.Totient.RSCountImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_positiveCount_majorant_finite {K T L : ℝ} {m : ℕ}
    (hK : 1 < K) (hKT : K ≤ T)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2)
    {H D : ℝ → ℝ} (hH : ∀ t ∈ Icc K T, HasDerivAt H (D t) t)
    (hD : ContinuousOn D (Icc K T))
    (hN : ∀ t ∈ Icc K T, (positiveCount t : ℝ) ≤ H t) :
    rsPositiveWindowSum (rsPhi m L) K T ≤
      (H K - (positiveCount K : ℝ)) * rsPhi m L K +
      ∫ t in K..T, D t * rsPhi m L t := by
  have hC : ContinuousOn H (uIcc K T) := by
    rw [uIcc_of_le hKT]
    exact fun t ht => (hH t ht).continuousAt.continuousWithinAt
  have hS : ContinuousOn (rsPhiSlope m L) (uIcc K T) := by
    rw [uIcc_of_le hKT]
    exact (rsPhiSlope_continuousOn m L).mono (fun _ ht => hK.trans_le ht.1)
  have hDi : ContinuousOn D (uIcc K T) := by rwa [uIcc_of_le hKT]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hH t ((uIcc_of_le hKT) ▸ ht))
    (fun t ht => rsPhi_hasDerivAt m L (hK.trans_le (((uIcc_of_le hKT) ▸ ht).1)))
    hDi.intervalIntegrable
    hS.intervalIntegrable
  have hcomp :
      (∫ t in K..T, H t * rsPhiSlope m L t) ≤
      ∫ t in K..T, (positiveCount t : ℝ) * rsPhiSlope m L t := by
    apply intervalIntegral.integral_mono_on hKT
      ((hC.mul hS).intervalIntegrable) (rs_count_phi_intervalIntegrable hK hKT m)
    intro t ht
    exact mul_le_mul_of_nonpos_right (hN t ht) (rsPhiSlope_nonpos hK ht.1 hupper)
  have hT := mul_le_mul_of_nonneg_right (hN T ⟨hKT, le_rfl⟩)
    (rsPhi_pos m L (by linarith : 0 < T)).le
  have hAbel := rs_positiveCount_phi_abel hK hKT m (L := L)
  nlinarith only [hparts, hcomp, hT, hAbel]

theorem rs_positiveCount_two_remainders_finite {K T L : ℝ} {m : ℕ}
    (hK : 1 < K) (hKT : K ≤ T)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2)
    {F E D : ℝ → ℝ}
    (hderiv : ∀ t ∈ Icc K T, HasDerivAt (fun u => F u + E u) (D t) t)
    (hD : ContinuousOn D (Icc K T))
    (hcount : ∀ t ∈ Icc K T, |(positiveCount t : ℝ) - F t| ≤ E t) :
    rsPositiveWindowSum (rsPhi m L) K T ≤
      2 * E K * rsPhi m L K + ∫ t in K..T, D t * rsPhi m L t := by
  have h := rs_positiveCount_majorant_finite hK hKT hupper hderiv hD
    (fun t ht => by have he := (abs_le.mp (hcount t ht)).2; linarith)
  have hlo := (abs_le.mp (hcount K ⟨le_rfl, hKT⟩)).1
  have hb : (F K + E K - (positiveCount K : ℝ)) * rsPhi m L K ≤
      2 * E K * rsPhi m L K :=
    mul_le_mul_of_nonneg_right (by linarith) (rsPhi_pos m L (by linarith)).le
  exact h.trans (add_le_add hb le_rfl)

theorem rs_positiveCount_two_remainders_infinite {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2)
    {F E D : ℝ → ℝ}
    (hderiv : ∀ t ∈ Ici K, HasDerivAt (fun u => F u + E u) (D t) t)
    (hD : ContinuousOn D (Ici K))
    (hcount : ∀ t ∈ Ici K, |(positiveCount t : ℝ) - F t| ≤ E t)
    (hI : IntegrableOn (fun t => D t * rsPhi m L t) (Ioi K)) :
    (∑' p, rsPositivePhiTerm K m L p) ≤
      2 * E K * rsPhi m L K + ∫ t in Ioi K, D t * rsPhi m L t := by
  apply le_of_tendsto_of_tendsto (rs_positiveWindow_phi_tendsto hK hL hm)
    ((intervalIntegral_tendsto_integral_Ioi K hI tendsto_id).const_add _)
  filter_upwards [eventually_ge_atTop K] with T hT
  exact rs_positiveCount_two_remainders_finite (by linarith [rsA_ge_thousand]) hT
    hupper (fun t ht => hderiv t ht.1) (hD.mono Icc_subset_Ici_self)
    (fun t ht => hcount t ht.1)

#print axioms rs_positiveCount_majorant_finite
#print axioms rs_positiveCount_two_remainders_finite
#print axioms rs_positiveCount_two_remainders_infinite

end LiuWang.Proof.Campaign20260915.Totient
