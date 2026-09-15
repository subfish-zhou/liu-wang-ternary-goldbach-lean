import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.RSConsumers

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex
open scoped ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.ZetaMomentTransport

theorem positiveHeightTail_eq_xi {K : ℝ} (hK : 0 ≤ K) {w : ℝ → ℝ}
    (hw : Summable (fun p => w |(riemannXiDivisorZeroValue p).im|)) :
    positiveHeightTail K w =
      ∑' p : RiemannXiDivisorZeroIndex,
        if K < (riemannXiDivisorZeroValue p).im then
          w (riemannXiDivisorZeroValue p).im else 0 := by
  classical
  have hs : Summable (fun p : RiemannXiDivisorZeroIndex =>
      if K < |(riemannXiDivisorZeroValue p).im| then
        w |(riemannXiDivisorZeroValue p).im| else 0) := by
    apply (hw.indicator {p | K < |(riemannXiDivisorZeroValue p).im|}).congr
    intro p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have ht := positive_weight_transport
    (f := fun z => if K < |z.im| then w |z.im| else 0) hs
  have hleft :
      (∑' p : RiemannXiDivisorZeroIndex,
        if 0 < (riemannXiDivisorZeroValue p).im then
          (if K < |(riemannXiDivisorZeroValue p).im| then
            w |(riemannXiDivisorZeroValue p).im| else 0) else 0) =
      ∑' p : RiemannXiDivisorZeroIndex,
        if K < (riemannXiDivisorZeroValue p).im then
          w (riemannXiDivisorZeroValue p).im else 0 := by
    apply tsum_congr
    intro p
    by_cases hp : 0 < (riemannXiDivisorZeroValue p).im
    · simp [hp, abs_of_pos hp]
    · have hk : ¬ K < (riemannXiDivisorZeroValue p).im :=
        not_lt.mpr ((not_lt.mp hp).trans hK)
      simp [hp, hk]
  rw [hleft] at ht
  refine (tsum_congr ?_).trans ht.symm
  intro z
  by_cases hp : 0 < (z : ℂ).im
  · simp [positiveZetaWeight, zetaWeight, hp, abs_of_pos hp]
  · simp [positiveZetaWeight, hp]

theorem rsHighTerm_sum_le_positive_xiPhi {K L : ℝ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m) :
    (∑' p, rsHighTerm K m L p) ≤
      2 * ∑' p : RiemannXiDivisorZeroIndex,
        if K < (riemannXiDivisorZeroValue p).im then
          rsPhi m L (riemannXiDivisorZeroValue p).im else 0 := by
  have hK0 : 0 ≤ K := by linarith [rsA_ge_thousand]
  rw [← positiveHeightTail_eq_xi hK0 (rsPhi_xi_summable hm hL)]
  exact rsHighTerm_sum_le_two_positivePhi hK hL hm

theorem rsZeroMoment_zero_eq_two_positive_xi {m : ℕ} (hm : 1 ≤ m) :
    (∑' p, rsZeroMoment m 0 p) =
      2 * ∑' p : RiemannXiDivisorZeroIndex,
        if 0 < (riemannXiDivisorZeroValue p).im then
          1 / (riemannXiDivisorZeroValue p).im ^ (m + 1) else 0 := by
  have hs : Summable (fun p : RiemannXiDivisorZeroIndex =>
      1 / |(riemannXiDivisorZeroValue p).im| ^ (m + 1)) := by
    apply (rsZeroMoment_summable hm (le_refl (0 : ℝ))).congr
    intro p
    simp only [rsZeroMoment, mul_zero, Real.exp_zero]
  simp only [rsZeroMoment, mul_zero, Real.exp_zero]
  rw [tsum_xi_eq_two_positive_xi (f := fun z => 1 / |z.im| ^ (m + 1))
    hs (fun z => by simp)]
  congr 1
  apply tsum_congr
  intro p
  by_cases hp : 0 < (riemannXiDivisorZeroValue p).im
  · simp [hp, abs_of_pos hp]
  · simp [hp]

theorem tsum_boundary_eq_atom (A : ℝ) (w : ℝ → ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex,
      if |(riemannXiDivisorZeroValue p).im| = A then
        w |(riemannXiDivisorZeroValue p).im| else 0) =
      2 * (boundaryMultiplicity A : ℝ) * w A := by
  classical
  have hs := tsum_closed_eq_sum A (fun z => if |z.im| = A then w |z.im| else 0)
  have he (p : RiemannXiDivisorZeroIndex) :
      (if |(riemannXiDivisorZeroValue p).im| ≤ A then
        (if |(riemannXiDivisorZeroValue p).im| = A then
          w |(riemannXiDivisorZeroValue p).im| else 0) else 0) =
      (if |(riemannXiDivisorZeroValue p).im| = A then
        w |(riemannXiDivisorZeroValue p).im| else 0) := by
    by_cases hp : |(riemannXiDivisorZeroValue p).im| = A
    · simp [hp]
    · simp [hp]
  simp_rw [he] at hs
  exact hs.trans (sum_closed_atom A w)

theorem tsum_closedTail_eq_open_add_atom {w : ℝ → ℝ}
    (hw : Summable (fun p => w |(riemannXiDivisorZeroValue p).im|)) (A : ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex,
      if A ≤ |(riemannXiDivisorZeroValue p).im| then
        w |(riemannXiDivisorZeroValue p).im| else 0) =
      (∑' p : RiemannXiDivisorZeroIndex,
        if A < |(riemannXiDivisorZeroValue p).im| then
          w |(riemannXiDivisorZeroValue p).im| else 0) +
      2 * (boundaryMultiplicity A : ℝ) * w A := by
  classical
  have hs : Summable (fun p : RiemannXiDivisorZeroIndex =>
      if A < |(riemannXiDivisorZeroValue p).im| then
        w |(riemannXiDivisorZeroValue p).im| else 0) := by
    apply (hw.indicator {p | A < |(riemannXiDivisorZeroValue p).im|}).congr
    intro p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have ha : Summable (fun p : RiemannXiDivisorZeroIndex =>
      if |(riemannXiDivisorZeroValue p).im| = A then
        w |(riemannXiDivisorZeroValue p).im| else 0) := by
    apply (hw.indicator {p | |(riemannXiDivisorZeroValue p).im| = A}).congr
    intro p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← tsum_boundary_eq_atom, ← hs.tsum_add ha]
  apply tsum_congr
  intro p
  rcases lt_trichotomy A |(riemannXiDivisorZeroValue p).im| with hp | hp | hp
  · simp [hp.le, hp, ne_of_gt hp]
  · simp [hp]
  · simp [not_le.mpr hp, not_lt.mpr hp.le, ne_of_lt hp]

theorem rsPhi_closedTail_eq_open_add_atom {m : ℕ} (hm : 1 ≤ m)
    {L : ℝ} (hL : 0 ≤ L) (A : ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex,
      if A ≤ |(riemannXiDivisorZeroValue p).im| then
        rsPhi m L |(riemannXiDivisorZeroValue p).im| else 0) =
      2 * positiveHeightTail A (rsPhi m L) +
      2 * (boundaryMultiplicity A : ℝ) * rsPhi m L A := by
  rw [tsum_closedTail_eq_open_add_atom (rsPhi_xi_summable hm hL),
    rsPhi_open_sum_eq_two hm hL]

#print axioms positiveHeightTail_eq_xi
#print axioms rsHighTerm_sum_le_positive_xiPhi
#print axioms rsZeroMoment_zero_eq_two_positive_xi
#print axioms tsum_boundary_eq_atom
#print axioms tsum_closedTail_eq_open_add_atom
#print axioms rsPhi_closedTail_eq_open_add_atom

end LiuWang.Proof.Campaign20260915.ZetaMomentTransport
