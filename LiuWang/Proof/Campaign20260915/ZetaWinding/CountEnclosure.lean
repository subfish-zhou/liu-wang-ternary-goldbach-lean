import LiuWang.Proof.Campaign20260915.ZetaWinding.HorizontalCount
import LiuWang.Proof.Campaign20260915.ZetaValidation.SignBlocks

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem winding_integer_unique {k m : ℤ} {d : ℂ}
    (hd : d = (k : ℂ) * (2 * Real.pi * I))
    (hw : |d.im - 2 * Real.pi * (m : ℝ)| < 2 * Real.pi) : k = m := by
  rw [hd] at hw
  simp only [mul_im, mul_re, intCast_re, intCast_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add] at hw
  norm_num at hw
  rw [abs_lt] at hw
  have hkm : (k : ℝ) < (m : ℝ) + 1 := by nlinarith [Real.pi_pos]
  have hmk : (m : ℝ) < (k : ℝ) + 1 := by nlinarith [Real.pi_pos]
  have hkm' : k < m + 1 := by exact_mod_cast hkm
  have hmk' : m < k + 1 := by exact_mod_cast hmk
  omega

section Segments

variable {H : ℝ} (hH : 0 < H) (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
  (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
  (hs : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)), 1 / 2 ≤ t)
  (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
    0 < (c j * riemannZeta (horizontalAt H t)).re)

include hH hx0 hxn hs hr

theorem zetaClosedCount_eq_of_winding_window (m : ℤ)
    (hw : |(horizontalPrimitiveSum H x c n -
        xiCountingPrimitive (horizontalAt H 2) +
        xiCountingPrimitive (horizontalAt H (1 / 2))).im -
          2 * Real.pi * (m : ℝ)| < 2 * Real.pi) :
    (zetaClosedCount H : ℝ) =
      2 * (xiCountingPrimitive (horizontalAt H (1 / 2))).im / Real.pi -
        4 * (m : ℝ) := by
  obtain ⟨k, hk, hc⟩ := zetaClosedCount_eq_winding hH x c n hx0 hxn hs hr
  have hd : horizontalPrimitiveSum H x c n -
      xiCountingPrimitive (horizontalAt H 2) +
      xiCountingPrimitive (horizontalAt H (1 / 2)) =
        (k : ℂ) * (2 * Real.pi * I) := by rw [hk]; ring
  rwa [winding_integer_unique hd hw] at hc

theorem zetaClosedCount_le_of_endpoint_upper (M : ℕ)
    (hu : 2 * (xiCountingPrimitive (horizontalAt H 2) -
        xiCountingPrimitive 2 - horizontalPrimitiveSum H x c n).im <
          ((M : ℝ) + 1) * Real.pi) :
    zetaClosedCount H ≤ M := by
  have hc := zetaClosedCount_eq_segment_sum hH x c n hx0 hxn hs hr
  have hlt : (zetaClosedCount H : ℝ) < (M : ℝ) + 1 := by
    rw [hc, div_lt_iff₀ Real.pi_pos]
    exact hu
  have hlt' : zetaClosedCount H < M + 1 := by exact_mod_cast hlt
  omega

end Segments

theorem zeta_values_and_orders_of_matching_witnesses {H : ℝ} (w : Finset ℂ)
    (hw : ∀ s ∈ w, riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ |s.im| ≤ H)
    (hc : zetaClosedCount H ≤ w.card) :
    zetaClosedValues H = w ∧
      ∀ s ∈ zetaClosedValues H, s.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta s = 1 := by
  classical
  have hsub : w ⊆ zetaClosedValues H := by
    intro s hs
    have hh := hw s hs
    apply mem_zetaClosedValues.mpr
    exact ⟨hh.1, by rw [hh.2.1]; norm_num, by rw [hh.2.1]; norm_num, hh.2.2⟩
  have hcard : (zetaClosedValues H).card ≤ w.card :=
    (zetaClosedValues_card_le_count H).trans hc
  have he : zetaClosedValues H = w :=
    (Finset.eq_of_subset_of_card_le hsub hcard).symm
  refine ⟨he, ?_⟩
  intro s hs
  refine ⟨(hw s (he ▸ hs)).2.1, ?_⟩
  have hp := zeta_order_positive_of_mem hs
  by_contra hn
  have hgt : 1 < analyticOrderNatAt riemannZeta s := by omega
  have hsum : ∑ _z ∈ zetaClosedValues H, (1 : ℕ) <
      ∑ z ∈ zetaClosedValues H, analyticOrderNatAt riemannZeta z :=
    Finset.sum_lt_sum (fun z hz => zeta_order_positive_of_mem hz) ⟨s, hs, hgt⟩
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  change (zetaClosedValues H).card < zetaClosedCount H at hsum
  rw [he] at hsum
  omega

theorem zeta_all_simple_of_segment_upper_and_witnesses {H : ℝ} (hH : 0 < H)
    (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
    (hs : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)), 1 / 2 ≤ t)
    (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
      0 < (c j * riemannZeta (horizontalAt H t)).re)
    (w : Finset ℂ)
    (hw : ∀ s ∈ w, riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ |s.im| ≤ H)
    (hu : 2 * (xiCountingPrimitive (horizontalAt H 2) -
        xiCountingPrimitive 2 - horizontalPrimitiveSum H x c n).im <
          ((w.card : ℝ) + 1) * Real.pi) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → |s.im| ≤ H →
      s.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta s = 1 := by
  have hc := zetaClosedCount_le_of_endpoint_upper hH x c n hx0 hxn hs hr w.card hu
  have he := zeta_values_and_orders_of_matching_witnesses w hw hc
  intro s hz h0 h1 ht
  exact he.2 s (mem_zetaClosedValues.mpr ⟨hz, h0, h1, ht⟩)

#print axioms winding_integer_unique
#print axioms zetaClosedCount_eq_of_winding_window
#print axioms zetaClosedCount_le_of_endpoint_upper
#print axioms zeta_values_and_orders_of_matching_witnesses
#print axioms zeta_all_simple_of_segment_upper_and_witnesses

end LiuWang.Proof.Campaign20260915.ZetaWinding
