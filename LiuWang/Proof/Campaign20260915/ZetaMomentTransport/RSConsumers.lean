import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.Windows
import LiuWang.Proof.Campaign20260915.Totient.RSEpsilonTerminal

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex
open scoped ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.ZetaMomentTransport

def positiveMoment (m : ℕ) (L : ℝ) : ℝ :=
  ∑' z, positiveZetaWeight (fun z =>
    Real.exp ((z.re - 1) * L) / z.im ^ (m + 1)) z

def positiveHeightTail (K : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∑' z, positiveZetaWeight (fun z => if K < z.im then w z.im else 0) z

theorem rsZeroMoment_eq_two_positive {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    (∑' p, rsZeroMoment m L p) = 2 * positiveMoment m L := by
  have hs := tsum_xi_eq_two_positive
    (f := fun z => Real.exp ((z.re - 1) * L) / |z.im| ^ (m + 1))
    (rsZeroMoment_summable hm hL) (fun z => by simp)
  simp only [rsZeroMoment]
  rw [hs]
  unfold positiveMoment
  congr 1
  apply tsum_congr
  intro z
  by_cases hp : 0 < (z : ℂ).im
  · simp [positiveZetaWeight, zetaWeight, hp, abs_of_pos hp]
  · simp [positiveZetaWeight, hp]

theorem rsZeroMoment_zero_eq_two_inverse {m : ℕ} (hm : 1 ≤ m) :
    (∑' p, rsZeroMoment m 0 p) =
      2 * ∑' z, positiveZetaWeight (fun z => 1 / z.im ^ (m + 1)) z := by
  rw [rsZeroMoment_eq_two_positive hm (le_refl 0)]
  simp only [positiveMoment, mul_zero, Real.exp_zero]

theorem rsHighTerm_eq_two_positive {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑' p, rsHighTerm K m L p) =
      2 * ∑' z, positiveZetaWeight (fun z => if K < z.im then
        Real.exp ((z.re - 1) * L) / z.im ^ (m + 1) else 0) z := by
  have hs := tsum_xi_eq_two_positive
    (f := fun z => if K < |z.im| then
      Real.exp ((z.re - 1) * L) / |z.im| ^ (m + 1) else 0)
    (rsHighTerm_summable hK hL hm) (fun z => by simp)
  simp only [rsHighTerm]
  rw [hs]
  congr 1
  apply tsum_congr
  intro z
  by_cases hp : 0 < (z : ℂ).im
  · simp [positiveZetaWeight, zetaWeight, hp, abs_of_pos hp]
  · simp [positiveZetaWeight, hp]

theorem rsPhi_xi_summable {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    Summable (fun p => rsPhi m L |(riemannXiDivisorZeroValue p).im|) := by
  apply Summable.of_nonneg_of_le (fun p => by unfold rsPhi; positivity)
    (f := rsZeroMoment m 0) _ (rsZeroMoment_summable hm (le_refl 0))
  intro p
  have ht := xi_zero_height_gt_one p
  simp only [rsPhi, rsZeroMoment, mul_zero, Real.exp_zero]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (div_nonneg hL (mul_pos rsR_pos (Real.log_pos ht)).le)

theorem rsPhi_open_sum_eq_two {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (K : ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex,
      if K < |(riemannXiDivisorZeroValue p).im| then
        rsPhi m L |(riemannXiDivisorZeroValue p).im| else 0) =
      2 * positiveHeightTail K (rsPhi m L) := by
  rw [tsum_open_eq_two_positive (f := fun z => rsPhi m L |z.im|)
    (rsPhi_xi_summable hm hL) (fun z => by simp) K]
  congr 1
  apply tsum_congr
  intro z
  by_cases hp : 0 < (z : ℂ).im
  · simp [positiveZetaWeight, zetaWeight, hp, abs_of_pos hp]
  · simp [positiveZetaWeight, hp]

theorem rsHighTerm_sum_le_two_positivePhi {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑' p, rsHighTerm K m L p) ≤ 2 * positiveHeightTail K (rsPhi m L) := by
  classical
  have hs : Summable (fun p : RiemannXiDivisorZeroIndex =>
      if K < |(riemannXiDivisorZeroValue p).im| then
        rsPhi m L |(riemannXiDivisorZeroValue p).im| else 0) := by
    apply ((rsPhi_xi_summable hm hL).indicator
      {p | K < |(riemannXiDivisorZeroValue p).im|}).congr
    intro p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  exact ((rsHighTerm_summable hK hL hm).tsum_le_tsum
    (rsHighTerm_le_phi hK hL m) hs).trans_eq (rsPhi_open_sum_eq_two hm hL K)

theorem rsHighTerm_sum_le_of_positive_budget {K L B : ℝ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m)
    (hB : positiveHeightTail K (rsPhi m L) ≤ B) :
    (∑' p, rsHighTerm K m L p) ≤ 2 * B :=
  (rsHighTerm_sum_le_two_positivePhi hK hL hm).trans
    (mul_le_mul_of_nonneg_left hB (by norm_num))

theorem rsZeroMoment_closed_open_exact {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (A : ℝ) :
    (∑' p, rsZeroMoment m L p) =
      (∑ p ∈ xiWindow 0 A, rsZeroMoment m L p) + ∑' p, rsHighTerm A m L p :=
  tsum_closed_open
    (f := fun z => Real.exp ((z.re - 1) * L) / |z.im| ^ (m + 1))
    (rsZeroMoment_summable hm hL) A

theorem rsZeroMoment_low_window_exact {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (A : ℝ) (hlow : ∀ z ∈ positiveValues A, z.re = 1 / 2) :
    (∑' p, rsZeroMoment m L p) =
      Real.exp (-L / 2) *
        (2 * ∑ z ∈ positiveValues A,
          (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ (m + 1)) +
      ∑' p, rsHighTerm A m L p := by
  rw [rsZeroMoment_closed_open_exact hm hL A]
  congr 1
  have hs := sum_closed_eq_two_positive A
    (fun z => Real.exp ((z.re - 1) * L) / |z.im| ^ (m + 1)) (fun z => by simp)
  simp only [rsZeroMoment]
  rw [hs]
  rw [mul_comm (Real.exp _), mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [hlow z hz, abs_of_pos (mem_positiveValues.mp hz).2.2.2.1,
    show ((1 / 2 : ℝ) - 1) * L = -L / 2 by ring]
  ring

theorem rsZeroMoment_inverse_atom (A : ℝ) (m : ℕ) :
    (∑ p ∈ xiWindow 0 A, if |(riemannXiDivisorZeroValue p).im| = A then
      rsZeroMoment m 0 p else 0) =
      2 * (boundaryMultiplicity A : ℝ) / A ^ (m + 1) := by
  simpa only [rsZeroMoment, mul_zero, Real.exp_zero, mul_one_div] using
    sum_closed_atom A (fun t => 1 / t ^ (m + 1))

theorem rsZeroMoment_low_high_of_positiveValues {m : ℕ} (hm : 1 ≤ m)
    {L : ℝ} (hL : 0 ≤ L)
    (hlow : ∀ z ∈ positiveValues rsA, z.re = 1 / 2) :
    (∑' p, rsZeroMoment m L p) ≤
      Real.exp (-L / 2) * (2 * positiveMoment m 0) +
      2 * positiveHeightTail rsA (rsPhi m L) := by
  have hb := rsZeroMoment_low_high hm hL ((low_window_iff_positiveValues rsA).mpr hlow)
  rw [rsZeroMoment_eq_two_positive hm (le_refl 0)] at hb
  exact hb.trans (add_le_add le_rfl (rsHighTerm_sum_le_two_positivePhi le_rfl hL hm))

theorem rsPsi_epsilon_of_positive_budgets {m : ℕ} (hm : 1 ≤ m)
    {δ a x k B : ℝ} (hδ : 0 < δ) (ha : 1 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x)
    (hlow : ∀ z ∈ positiveValues rsA, z.re = 1 / 2)
    (hk : positiveMoment m 0 ≤ k)
    (hhigh : positiveHeightTail rsA (rsPhi m (Real.log a)) ≤ B)
    (hbudget : Real.exp (-Real.log a / 2) * (2 * k) + 2 * B ≤ (δ / 2) ^ (m + 1)) :
    x * (1 - rsEpsilon m δ) - 1.84 < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + rsEpsilon m δ) - (1 / 2) * Real.log (1 - x⁻¹ ^ 2) := by
  apply rsPsi_delta_epsilon_of_low_window_and_high_sum hm hδ ha hcut hax
    ((low_window_iff_positiveValues rsA).mpr hlow) (k := 2 * k) (B := 2 * B) _ _ hbudget
  · rw [rsZeroMoment_eq_two_positive hm (le_refl 0)]
    exact mul_le_mul_of_nonneg_left hk (by norm_num)
  · exact rsHighTerm_sum_le_of_positive_budget le_rfl (Real.log_nonneg ha.le) hm hhigh

#print axioms rsZeroMoment_eq_two_positive
#print axioms rsZeroMoment_zero_eq_two_inverse
#print axioms rsHighTerm_eq_two_positive
#print axioms rsPhi_xi_summable
#print axioms rsHighTerm_sum_le_two_positivePhi
#print axioms rsZeroMoment_low_window_exact
#print axioms rsZeroMoment_inverse_atom
#print axioms rsZeroMoment_low_high_of_positiveValues
#print axioms rsPsi_epsilon_of_positive_budgets

end LiuWang.Proof.Campaign20260915.ZetaMomentTransport
