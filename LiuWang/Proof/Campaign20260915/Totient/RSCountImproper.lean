import LiuWang.Proof.Campaign20260915.Totient.RSCountLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_count_phi_intervalIntegrable {K T L : ℝ} (hK : 1 < K)
    (hKT : K ≤ T) (m : ℕ) :
    IntervalIntegrable (fun t => (positiveCount t : ℝ) * rsPhiSlope m L t)
      volume K T := by
  apply (positiveCount_intervalIntegrable K T).mul_continuousOn
  rw [uIcc_of_le hKT]
  exact (rsPhiSlope_continuousOn m L).mono (fun _ ht => hK.trans_le ht.1)

theorem rs_count_phi_integral_tendsto {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m) :
    Tendsto (fun T => ∫ t in K..T, (positiveCount t : ℝ) * rsPhiSlope m L t) atTop
      (𝓝 (-(positiveCount K : ℝ) * rsPhi m L K - ∑' p, rsPositivePhiTerm K m L p)) := by
  have h := ((rs_positiveCount_phi_tendsto hL hm).sub_const
    ((positiveCount K : ℝ) * rsPhi m L K)).sub (rs_positiveWindow_phi_tendsto hK hL hm)
  simp only [zero_sub, neg_mul] at h ⊢
  apply h.congr'
  filter_upwards [eventually_ge_atTop K] with T hT
  have hAbel := rs_positiveCount_phi_abel (by linarith [rsA_ge_thousand] : 1 < K) hT m
    (L := L)
  linarith

theorem rs_count_phi_integrableOn {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2) :
    IntegrableOn (fun t => (positiveCount t : ℝ) * rsPhiSlope m L t) (Ioi K) := by
  have hK1 : 1 < K := by linarith [rsA_ge_thousand]
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto
    (- (-(positiveCount K : ℝ) * rsPhi m L K - ∑' p, rsPositivePhiTerm K m L p))
    K (b := id) (l := atTop)
  · intro T
    change IntegrableOn (fun t => (positiveCount t : ℝ) * rsPhiSlope m L t) (Ioc K T)
    by_cases hT : K ≤ T
    · exact (rs_count_phi_intervalIntegrable hK1 hT m).1
    · simp only [Ioc_eq_empty_of_le (not_le.mp hT).le, integrableOn_empty]
  · exact tendsto_id
  · apply (rs_count_phi_integral_tendsto hK hL hm).neg.congr'
    filter_upwards [eventually_ge_atTop K] with T hT
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' := (uIcc_of_le hT) ▸ ht
    have hn : (positiveCount t : ℝ) * rsPhiSlope m L t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
        (rsPhiSlope_nonpos hK1 ht'.1 hupper)
    exact (Real.norm_of_nonpos hn).symm

theorem rs_positiveCount_phi_abel_infinite {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2) :
    (∑' p, rsPositivePhiTerm K m L p) =
      -(positiveCount K : ℝ) * rsPhi m L K -
      ∫ t in Ioi K, (positiveCount t : ℝ) * rsPhiSlope m L t := by
  have he := tendsto_nhds_unique (rs_count_phi_integral_tendsto hK hL hm)
    (intervalIntegral_tendsto_integral_Ioi K
      (rs_count_phi_integrableOn hK hL hm hupper) tendsto_id)
  linarith

#print axioms rs_count_phi_intervalIntegrable
#print axioms rs_count_phi_integral_tendsto
#print axioms rs_count_phi_integrableOn
#print axioms rs_positiveCount_phi_abel_infinite

end LiuWang.Proof.Campaign20260915.Totient
