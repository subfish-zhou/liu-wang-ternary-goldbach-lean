import LiuWang.Proof.NearOneDensity.Quadratic

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical

namespace LiuWang.Proof.NearOneDensity

theorem series_quadratic {ι ν : Type*} (s : Finset ι)
    (w : ν → ℝ) (v : ι → ν → ℂ) (hw : ∀ n, 0 ≤ w n)
    (hsw : Summable w)
    (hsv : ∀ i ∈ s, Summable (fun n => w n * (v i n).re))
    (hsk : ∀ i ∈ s, ∀ j ∈ s,
      Summable (fun n => w n * (v i n * conj (v j n)).re)) :
    (∑ i ∈ s, ∑' n, w n * (v i n).re) ^ 2 ≤
      (∑' n, w n) * ∑ i ∈ s, ∑ j ∈ s,
        ∑' n, w n * (v i n * conj (v j n)).re := by
  have hleft := (tendsto_finsetSum s (fun i hi => (hsv i hi).hasSum)).pow 2
  have hright := Filter.Tendsto.mul hsw.hasSum
    (tendsto_finsetSum s (fun i hi =>
      tendsto_finsetSum s (fun j hj => (hsk i hi j hj).hasSum)))
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall (fun u => weighted_quadratic s u w v (fun n _ => hw n)))

theorem count_of_series {ι ν : Type*} (s : Finset ι)
    (w : ν → ℝ) (v : ι → ν → ℂ) (hw : ∀ n, 0 ≤ w n)
    (hsw : Summable w)
    (hsv : ∀ i ∈ s, Summable (fun n => w n * (v i n).re))
    (hsk : ∀ i ∈ s, ∀ j ∈ s,
      Summable (fun n => w n * (v i n * conj (v j n)).re))
    {A B D : ℝ} (hA : 0 ≤ A) (hBA : B ≤ A) (hD : 0 ≤ D)
    (hmass : (∑' n, w n) ≤ A)
    (hzero : ∀ i ∈ s, (∑' n, w n * (v i n).re) ≤ -D)
    (hdiag : ∀ i ∈ s, (∑' n, w n * (v i n * conj (v i n)).re) ≤ A)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∑' n, w n * (v i n * conj (v j n)).re) ≤ B)
    (hgap : 0 < D ^ 2 - A * B) :
    (s.card : ℝ) ≤ (A ^ 2 - A * B) / (D ^ 2 - A * B) := by
  let K := fun i j => ∑' n, w n * (v i n * conj (v j n)).re
  have hK : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, K i j := by
    have hex : (∑' n, w n * gram s (fun i => v i n)) =
        ∑ i ∈ s, ∑ j ∈ s, K i j := by
      simp only [gram, Finset.mul_sum]
      rw [Summable.tsum_finsetSum (fun i hi =>
        summable_sum (fun j hj => hsk i hi j hj))]
      exact Finset.sum_congr rfl (fun i hi => Summable.tsum_finsetSum (hsk i hi))
    rw [← hex]
    exact tsum_nonneg (fun n => mul_nonneg (hw n) (gram_nonneg s _))
  apply heath_brown_count hA hBA hD
  · calc
      _ ≤ ∑ _i ∈ s, -D := Finset.sum_le_sum hzero
      _ = -D * s.card := by simp [mul_comm]
  · calc
      _ ≤ (∑' n, w n) * ∑ i ∈ s, ∑ j ∈ s, K i j :=
        series_quadratic s w v hw hsw hsv hsk
      _ ≤ A * ∑ i ∈ s, ∑ j ∈ s, K i j := mul_le_mul_of_nonneg_right hmass hK
      _ ≤ A * (A * s.card + B * ((s.card : ℝ) ^ 2 - s.card)) :=
        mul_le_mul_of_nonneg_left (pair_sum_le s K A B hdiag hoff) hA
  · exact hgap

end LiuWang.Proof.NearOneDensity
