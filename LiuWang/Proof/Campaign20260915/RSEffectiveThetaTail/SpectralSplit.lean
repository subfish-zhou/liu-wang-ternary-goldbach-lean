import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.SmoothingParameters
import LiuWang.Proof.PrincipalPsi.Quantitative.HeightSelection

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem actual_high_spectrum_split {L K : ℝ} (hL : 0 ≤ L) (hK : rsA ≤ K) :
    (∑' p, rsHighTerm rsA 1 L p) =
      (∑ p ∈ xiWindow 0 K, rsHighTerm rsA 1 L p) + ∑' p, rsHighTerm K 1 L p := by
  classical
  let f (p : RiemannXiDivisorZeroIndex) : ℝ :=
    if p ∈ xiWindow 0 K then rsHighTerm rsA 1 L p else 0
  have hf : Summable f := by
    apply summable_of_ne_finset_zero (s := xiWindow 0 K)
    intro p hp
    simp only [f, if_neg hp]
  have hpoint (p : RiemannXiDivisorZeroIndex) :
      rsHighTerm rsA 1 L p = f p + rsHighTerm K 1 L p := by
    by_cases hp : p ∈ xiWindow 0 K
    · have ht : |(riemannXiDivisorZeroValue p).im| ≤ K := by
        simpa only [mem_xiWindow, sub_zero] using hp
      simp only [f, if_pos hp, rsHighTerm, if_neg (not_lt.mpr ht), add_zero]
    · have ht : K < |(riemannXiDivisorZeroValue p).im| := by
        have hn : ¬ |(riemannXiDivisorZeroValue p).im| ≤ K := by
          simpa only [mem_xiWindow, sub_zero] using hp
        exact lt_of_not_ge hn
      simp only [f, if_neg hp, rsHighTerm, if_pos ht, if_pos (hK.trans_lt ht), zero_add]
  rw [tsum_congr hpoint, hf.tsum_add (rsHighTerm_summable hK hL (by norm_num))]
  congr 1
  rw [tsum_eq_sum (s := xiWindow 0 K) (by
    intro p hp
    simp only [f, if_neg hp])]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [f, if_pos hp]

theorem actual_selected_high_spectrum {L : ℝ} (hL : 5000 ≤ L) :
    (∑' p, rsHighTerm rsA 1 L p) ≤
      (xiWindow 0 (spectralCutoff L)).card * Real.exp (-2 * Real.sqrt 2 * saddle L) +
        ∑' p, rsHighTerm (spectralCutoff L) 1 L p := by
  have hL0 : 0 ≤ L := by linarith
  rw [actual_high_spectrum_split hL0 (spectralCutoff_ge_rsA hL)]
  exact add_le_add (actual_finite_spectrum_le_peak hL0 _) le_rfl

#print axioms actual_high_spectrum_split
#print axioms actual_selected_high_spectrum

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
