import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.Multiplicity

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex
open scoped ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.ZetaMomentTransport

def zetaConjugation : ZetaZero ≃ ZetaZero where
  toFun z := ⟨conj (z : ℂ), by
    exact ⟨by rw [riemannZeta_conj, z.property.1, map_zero],
      by simpa using z.property.2.1, by simpa using z.property.2.2⟩⟩
  invFun z := ⟨conj (z : ℂ), by
    exact ⟨by rw [riemannZeta_conj, z.property.1, map_zero],
      by simpa using z.property.2.1, by simpa using z.property.2.2⟩⟩
  left_inv z := Subtype.ext (Complex.conj_conj _)
  right_inv z := Subtype.ext (Complex.conj_conj _)

theorem zetaWeight_conjugation {f : ℂ → ℝ}
    (he : ∀ z : ℂ, f (conj z) = f z) (z : ZetaZero) :
    zetaWeight f (zetaConjugation z) = zetaWeight f z := by
  change (analyticOrderNatAt riemannZeta (conj (z : ℂ)) : ℝ) * f (conj (z : ℂ)) = _
  rw [zeta_order_conj z.property.2.1 z.property.2.2, he]
  rfl

theorem positiveZetaWeight_summable {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p))) :
    Summable (positiveZetaWeight f) :=
  (hasSum_zetaWeight hf).summable.indicator {z | 0 < (z : ℂ).im}

theorem tsum_xi_eq_two_positive {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p)))
    (he : ∀ z : ℂ, f (conj z) = f z) :
    (∑' p, f (riemannXiDivisorZeroValue p)) =
      2 * ∑' z, positiveZetaWeight f z := by
  classical
  let negWeight : ZetaZero → ℝ := fun z =>
    if ¬ 0 < (z : ℂ).im then zetaWeight f z else 0
  have hn : Summable negWeight := by
    apply ((hasSum_zetaWeight hf).summable.indicator
      {z | ¬ 0 < (z : ℂ).im}).congr
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, negWeight]
  have hneg : (∑' z, negWeight z) = ∑' z, positiveZetaWeight f z := by
    rw [← zetaConjugation.tsum_eq negWeight]
    apply tsum_congr
    intro z
    have hz := zetaZero_im_ne_zero z
    change (if ¬ 0 < -(z : ℂ).im then
      zetaWeight f (zetaConjugation z) else 0) = _
    rw [zetaWeight_conjugation he]
    by_cases hp : 0 < (z : ℂ).im
    · simp [positiveZetaWeight, hp, not_lt.mpr (neg_nonpos.mpr hp.le)]
    · have hlt : (z : ℂ).im < 0 := lt_of_le_of_ne (not_lt.mp hp) hz
      simp [positiveZetaWeight, hp, neg_pos.mpr hlt]
  calc
    _ = ∑' z, zetaWeight f z := tsum_xi_eq_zetaWeight hf
    _ = (∑' z, positiveZetaWeight f z) + ∑' z, negWeight z := by
      rw [← (positiveZetaWeight_summable hf).tsum_add hn]
      apply tsum_congr
      intro z
      by_cases hp : 0 < (z : ℂ).im <;> simp [positiveZetaWeight, negWeight, hp]
    _ = _ := by rw [hneg]; ring

theorem tsum_xi_eq_two_positive_xi {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p)))
    (he : ∀ z : ℂ, f (conj z) = f z) :
    (∑' p, f (riemannXiDivisorZeroValue p)) =
      2 * ∑' p : RiemannXiDivisorZeroIndex,
        if 0 < (riemannXiDivisorZeroValue p).im then
          f (riemannXiDivisorZeroValue p) else 0 := by
  rw [positive_weight_transport hf]
  exact tsum_xi_eq_two_positive hf he

theorem tsum_even_height {w : ℝ → ℝ}
    (hw : ∀ t, w (-t) = w t)
    (hs : Summable (fun p => w (riemannXiDivisorZeroValue p).im)) :
    (∑' p, w (riemannXiDivisorZeroValue p).im) =
      2 * ∑' z, positiveZetaWeight (fun z => w z.im) z :=
  tsum_xi_eq_two_positive (f := fun z => w z.im) hs (fun z => by simpa using hw z.im)

theorem summable_closed (A : ℝ) (f : ℂ → ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      if |(riemannXiDivisorZeroValue p).im| ≤ A then
        f (riemannXiDivisorZeroValue p) else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := xiWindow 0 A)
  intro p hp
  have hn : ¬ |(riemannXiDivisorZeroValue p).im| ≤ A := by
    simpa only [mem_xiWindow, sub_zero] using hp
  simp [hn]

theorem tsum_closed_eq_sum (A : ℝ) (f : ℂ → ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex,
      if |(riemannXiDivisorZeroValue p).im| ≤ A then
        f (riemannXiDivisorZeroValue p) else 0) =
      ∑ p ∈ xiWindow 0 A, f (riemannXiDivisorZeroValue p) := by
  classical
  rw [tsum_eq_sum (s := xiWindow 0 A) (by
    intro p hp
    have hn : ¬ |(riemannXiDivisorZeroValue p).im| ≤ A := by
      simpa only [mem_xiWindow, sub_zero] using hp
    simp [hn])]
  apply Finset.sum_congr rfl
  intro p hp
  have hm : |(riemannXiDivisorZeroValue p).im| ≤ A := by
    simpa only [mem_xiWindow, sub_zero] using hp
  simp [hm]

theorem positive_closed_transport (A : ℝ) (f : ℂ → ℝ) :
    (∑' z, positiveZetaWeight (fun z => if |z.im| ≤ A then f z else 0) z) =
      ∑ z ∈ positiveValues A, (analyticOrderNatAt riemannZeta z : ℝ) * f z := by
  classical
  rw [← positive_weight_transport (f := fun z => if |z.im| ≤ A then f z else 0)
    (summable_closed A f)]
  have he (p : RiemannXiDivisorZeroIndex) :
      (if 0 < (riemannXiDivisorZeroValue p).im then
        if |(riemannXiDivisorZeroValue p).im| ≤ A then
          f (riemannXiDivisorZeroValue p) else 0 else 0) =
      (if |(riemannXiDivisorZeroValue p).im| ≤ A then
        if 0 < (riemannXiDivisorZeroValue p).im then
          f (riemannXiDivisorZeroValue p) else 0 else 0) := by
    split_ifs <;> rfl
  simp_rw [he]
  rw [tsum_closed_eq_sum A (fun z => if 0 < z.im then f z else 0),
    sum_xiWindow_eq_zeta A (fun z => if 0 < z.im then f z else 0)]
  simp only [positiveValues, Finset.sum_filter, mul_ite, mul_zero]

theorem sum_closed_eq_two_positive (A : ℝ) (f : ℂ → ℝ)
    (he : ∀ z : ℂ, f (conj z) = f z) :
    (∑ p ∈ xiWindow 0 A, f (riemannXiDivisorZeroValue p)) =
      2 * ∑ z ∈ positiveValues A, (analyticOrderNatAt riemannZeta z : ℝ) * f z := by
  have ht := tsum_xi_eq_two_positive (f := fun z => if |z.im| ≤ A then f z else 0)
    (summable_closed A f) (fun z => by simp [he])
  rwa [tsum_closed_eq_sum, positive_closed_transport] at ht

theorem sum_height_window (A T : ℝ) (w : ℝ → ℝ) :
    (∑ p ∈ xiWindow 0 T, if A < |(riemannXiDivisorZeroValue p).im| then
      w |(riemannXiDivisorZeroValue p).im| else 0) =
      2 * ∑ z ∈ (positiveValues T).filter (fun z => A < z.im),
        (analyticOrderNatAt riemannZeta z : ℝ) * w z.im := by
  classical
  rw [sum_closed_eq_two_positive T
    (fun z => if A < |z.im| then w |z.im| else 0) (fun z => by simp),
    Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [abs_of_pos (mem_positiveValues.mp hz).2.2.2.1]
  split_ifs <;> simp

theorem tsum_closed_open {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p))) (A : ℝ) :
    (∑' p, f (riemannXiDivisorZeroValue p)) =
      (∑ p ∈ xiWindow 0 A, f (riemannXiDivisorZeroValue p)) +
      ∑' p : RiemannXiDivisorZeroIndex,
        if A < |(riemannXiDivisorZeroValue p).im| then
          f (riemannXiDivisorZeroValue p) else 0 := by
  classical
  have hh : Summable (fun p => if A < |(riemannXiDivisorZeroValue p).im| then
      f (riemannXiDivisorZeroValue p) else 0) := by
    apply (hf.indicator {p | A < |(riemannXiDivisorZeroValue p).im|}).congr
    intro p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← tsum_closed_eq_sum, ← (summable_closed A f).tsum_add hh]
  apply tsum_congr
  intro p
  by_cases hp : |(riemannXiDivisorZeroValue p).im| ≤ A
  · simp [hp, not_lt.mpr hp]
  · simp [hp, lt_of_not_ge hp]

theorem tsum_open_eq_two_positive {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p)))
    (he : ∀ z : ℂ, f (conj z) = f z) (A : ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex,
      if A < |(riemannXiDivisorZeroValue p).im| then
        f (riemannXiDivisorZeroValue p) else 0) =
      2 * ∑' z, positiveZetaWeight (fun z => if A < z.im then f z else 0) z := by
  classical
  have hs : Summable (fun p => if A < |(riemannXiDivisorZeroValue p).im| then
      f (riemannXiDivisorZeroValue p) else 0) := by
    apply (hf.indicator {p | A < |(riemannXiDivisorZeroValue p).im|}).congr
    intro p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [tsum_xi_eq_two_positive (f := fun z => if A < |z.im| then f z else 0)
    hs (fun z => by simp [he])]
  congr 1
  apply tsum_congr
  intro z
  by_cases hp : 0 < (z : ℂ).im
  · simp [positiveZetaWeight, zetaWeight, hp, abs_of_pos hp]
  · simp [positiveZetaWeight, hp]

theorem sum_closed_atom (A : ℝ) (w : ℝ → ℝ) :
    (∑ p ∈ xiWindow 0 A,
      if |(riemannXiDivisorZeroValue p).im| = A then
        w |(riemannXiDivisorZeroValue p).im| else 0) =
      2 * (boundaryMultiplicity A : ℝ) * w A := by
  classical
  rw [sum_closed_eq_two_positive A
    (fun z => if |z.im| = A then w |z.im| else 0) (fun z => by simp)]
  have he :
      (∑ z ∈ positiveValues A, (analyticOrderNatAt riemannZeta z : ℝ) *
        (if |z.im| = A then w |z.im| else 0)) =
      (boundaryMultiplicity A : ℝ) * w A := by
    rw [boundaryMultiplicity, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    have hp := (mem_positiveValues.mp hz).2.2.2.1
    rw [abs_of_pos hp]
    by_cases ha : z.im = A <;> simp [ha]
  rw [he]
  ring

theorem sum_closed_strict_atom (A : ℝ) (w : ℝ → ℝ) :
    (∑ p ∈ xiWindow 0 A, w |(riemannXiDivisorZeroValue p).im|) =
      (∑ p ∈ (xiWindow 0 A).filter (fun p =>
        |(riemannXiDivisorZeroValue p).im| < A), w |(riemannXiDivisorZeroValue p).im|) +
      2 * (boundaryMultiplicity A : ℝ) * w A := by
  classical
  rw [← sum_closed_atom A w, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hle : |(riemannXiDivisorZeroValue p).im| ≤ A := by
    simpa only [mem_xiWindow, sub_zero] using hp
  rcases lt_or_eq_of_le hle with hlt | he
  · simp [hlt, ne_of_lt hlt]
  · simp [he]

#print axioms tsum_xi_eq_two_positive
#print axioms tsum_even_height
#print axioms tsum_closed_open
#print axioms tsum_open_eq_two_positive
#print axioms sum_closed_atom
#print axioms sum_closed_strict_atom

end LiuWang.Proof.Campaign20260915.ZetaMomentTransport
