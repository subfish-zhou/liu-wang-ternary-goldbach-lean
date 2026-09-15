import LiuWang.Proof.Campaign20260915.ZetaWinding.SignMatching

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

section Data

variable {H : ℝ} (hH : 16 ≤ H)
  (x : ℕ → ℝ) (c z : ℕ → ℂ) (e L : ℕ → ℝ) (n : ℕ)
  (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
  (hxlo : ∀ j < n, 1 / 2 ≤ x j)
  (hxstep : ∀ j < n, x j ≤ x (j + 1))
  (hL : ∀ j < n, 0 ≤ L j)
  (he : ∀ j < n, ‖riemannZeta (horizontalAt H (x j)) - z j‖ ≤ e j)
  (hd : ∀ j < n, ∀ t ∈ Set.Icc (x j) (x (j + 1)),
    ‖deriv riemannZeta (horizontalAt H t)‖ ≤ L j)
  (hm : ∀ j < n,
    ‖c j‖ * (e j + L j * (x (j + 1) - x j)) < (c j * z j).re)
  {m : ℕ} (l r : Fin m → ℝ)
  (hlo : ∀ i, 16 ≤ l i) (hhi : ∀ i, r i ≤ H)
  (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
  (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0)
  (hu : 2 * (xiCountingPrimitive (horizontalAt H 2) -
    xiCountingPrimitive 2 - horizontalPrimitiveSum H x c n).im <
      (3 + 2 * (m : ℝ)) * Real.pi)

include hH hx0 hxn hxlo hxstep hL he hd hm hlo hhi hwidth hsep hsign hu

theorem zeta_all_simple_of_endpoint_data :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → |s.im| ≤ H →
      s.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta s = 1 := by
  apply zeta_all_simple_of_segments_and_signs hH x c n hx0 hxn
    ?_ ?_ l r hlo hhi hwidth hsep hsign hu
  · intro j hj t ht
    rw [Set.uIcc_of_le (hxstep j hj)] at ht
    exact (hxlo j hj).trans ht.1
  · intro j hj t ht
    rw [Set.uIcc_of_le (hxstep j hj)] at ht
    exact horizontal_rotated_pos_of_endpoint_deriv (by linarith)
      (hL j hj) (he j hj) (hd j hj) (hm j hj) t ht

theorem original_strict_height_of_endpoint_data (hheight : 1894438 ≤ H) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      16 < |s.im| → |s.im| < 1894438 → s.re = 1 / 2 := by
  intro s hz h0 h1 _ ht
  exact (zeta_all_simple_of_endpoint_data hH x c z e L n hx0 hxn hxlo hxstep
    hL he hd hm l r hlo hhi hwidth hsep hsign hu s hz h0 h1 (ht.le.trans hheight)).1

end Data

#print axioms zeta_all_simple_of_endpoint_data
#print axioms original_strict_height_of_endpoint_data

end LiuWang.Proof.Campaign20260915.ZetaWinding
