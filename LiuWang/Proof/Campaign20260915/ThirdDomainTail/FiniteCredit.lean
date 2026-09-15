import LiuWang.Proof.SourceRoute.ThirdArc.PartialSummation

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.SourceRoute.ThirdArc

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem integral_height_closed_tail {u r v : ℝ} (hu : 0 < u)
    (hur : u ≤ r) (hrv : r ≤ v) (p : ℝ) :
    (∫ y in u..v, (Set.Ici r).indicator (heightKernel p) y) =
      r ^ (-p) - v ^ (-p) := by
  have he : (Set.Ioi r).indicator (heightKernel p) =ᵐ[volume]
      (Set.Ici r).indicator (heightKernel p) :=
    indicator_ae_eq_of_ae_eq_set Ioi_ae_eq_Ici
  calc
    _ = ∫ y in u..v, (Set.Ioi r).indicator (heightKernel p) y :=
      intervalIntegral.integral_congr_ae (he.symm.mono (fun _ hy _ => hy))
    _ = _ := integral_height_tail hu hur hrv p

theorem finite_height_partialSummation_eq {ι : Type*} (s : Finset ι)
    (r w : ι → ℝ) {u v p : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hr : ∀ i ∈ s, u ≤ r i ∧ r i ≤ v) :
    (∑ i ∈ s, w i * r i ^ (-p)) =
      v ^ (-p) * (∑ i ∈ s, w i) +
        ∫ y in u..v, heightKernel p y * cumulative s r w y := by
  simp_rw [cumulative_integrand]
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => (indicator_integrable (heightKernel_integrable hu huv p)
      measurableSet_Ici).const_mul (w i))]
  simp only [intervalIntegral.integral_const_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_height_closed_tail hu (hr i hi).1 (hr i hi).2]
  ring

theorem cumulative_zero_height_credit {u v p C : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    v ^ (-p) * C + (∫ y in u..v, heightKernel p y * C) = u ^ (-p) * C := by
  rw [intervalIntegral.integral_mul_const, integral_heightKernel hu huv p]
  ring

#print axioms finite_height_partialSummation_eq
#print axioms cumulative_zero_height_credit

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
