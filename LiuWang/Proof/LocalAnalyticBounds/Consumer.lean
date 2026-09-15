import LiuWang.Proof.LocalAnalyticBounds.Main

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.LocalAnalyticBounds

example {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : Complex} (hz : a ≤ z.re) {N : Nat} (hN : 1 ≤ N) :
    ‖Complex.digamma z - digammaApprox z N‖ ≤ ‖z - 1‖ / (a * N) :=
  norm_digamma_sub_approx_le ha ha1 hz hN

example {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : Complex} (hz : a ≤ z.re) {N : Nat} (hN : 1 ≤ N) :
    (Complex.digamma z).re ∈
      Set.Icc ((digammaApprox z N).re - ‖z - 1‖ / (a * N))
        ((digammaApprox z N).re + ‖z - 1‖ / (a * N)) :=
  digamma_re_mem_approx_interval ha ha1 hz hN

example {q : Nat} {chi : Character q} (he : DirichletCharacter.Even chi)
    {a : Real} (ha : 0 < a) (ha1 : a ≤ 1) {s : Complex} (hs : a ≤ (s / 2).re)
    {N : Nat} (hN : 1 ≤ N) :
    ‖logDeriv chi.gammaFactor s - gammaFactorApprox (s / 2) N‖ ≤
      ‖s / 2 - 1‖ / (2 * a * N) :=
  norm_logDeriv_gammaFactor_sub_approx_even_le he ha ha1 hs hN

example {q : Nat} {chi : Character q} (ho : DirichletCharacter.Odd chi)
    {a : Real} (ha : 0 < a) (ha1 : a ≤ 1) {s : Complex} (hspos : 0 < s.re)
    (hs : a ≤ ((s + 1) / 2).re) {N : Nat} (hN : 1 ≤ N) :
    ‖logDeriv chi.gammaFactor s - gammaFactorApprox ((s + 1) / 2) N‖ ≤
      ‖(s + 1) / 2 - 1‖ / (2 * a * N) :=
  norm_logDeriv_gammaFactor_sub_approx_odd_le ho ha ha1 hspos hs hN

example {T : Real} {rho : Complex} (hr : rho.re ∈ Set.Icc 0 1)
    (ht : |T - rho.im| ≤ 1) :
    (2 : Real) / 5 ≤ (1 / (referencePoint T - rho)).re :=
  two_fifths_le_reference_kernel hr ht

example {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi) (T : Real) :
    (closedZeroWindow chi T).Finite :=
  finite_closedZeroWindow hchi hp T

example {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ((closedZeroWindow chi T).ncard : Real) ≤ (5 / 2 : Real) *
      ∑' p : CompletedZeroIndex chi, (1 / (referencePoint T - completedZeroValue p)).re :=
  ncard_closedZeroWindow_le_reference_kernel hchi hp T

example {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ((closedZeroWindow chi T).ncard : Real) ≤ (5 / 2 : Real) *
      (Real.log q / 2 + (logDeriv chi.gammaFactor (referencePoint T)).re +
        ‖-deriv riemannZeta (2 : Complex) / riemannZeta (2 : Complex)‖) :=
  ncard_closedZeroWindow_le_gamma_zeta hchi hp T

example {z : Complex} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) :
    (Complex.digamma z).re ≤ Real.log (|z.im| + 2) + 2 :=
  digamma_re_le_log_add_two hlo hhi

example {q : Nat} (chi : Character q) {s : Complex} (hs : s.re = 2) :
    (logDeriv chi.gammaFactor s).re ≤ Real.log (|s.im| + 2) / 2 + 1 :=
  logDeriv_gammaFactor_re_le_on_two chi hs

example : ‖-deriv riemannZeta (2 : Complex) / riemannZeta (2 : Complex)‖ ≤ 6 :=
  norm_neg_logDeriv_zeta_two_le_six

example {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ((closedZeroWindow chi T).ncard : Real) ≤ (5 / 2 : Real) *
      (Real.log q / 2 + Real.log (|T| + 2) / 2 + 7) :=
  ncard_closedZeroWindow_le_explicit hchi hp T

example {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ((closedZeroWindow chi T).ncard : Real) ≤
        3.5 * (0.5 * Real.log ((q : Real) * (T + 2)) + 0.59773) ∧
      ((closedZeroWindow chi T).ncard : Real) ≤
        1.7769 * Real.log ((q : Real) * T) - 1 :=
  ncard_closedZeroWindow_source_bound hq hchi hp hT

example {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi) :
    ((closedZeroWindow chi ((2000 : Real) ^ (15 : Nat))).ncard : Real) ≤
      1.7769 * Real.log ((q : Real) * (2000 : Real) ^ (15 : Nat)) - 1 :=
  (ncard_closedZeroWindow_source_bound hq hchi hp le_rfl).2

example {q : Nat} [NeZero q] {chi : Character q} {T : Real} (p : CompletedZeroIndex chi)
    (h : |T - (completedZeroValue p).im| = 1) :
    p ∈ closedZeroWindow chi T :=
  h.le

example (T : Real) : (2 : Real) / 5 ≤
    (1 / (referencePoint T - (0 + ((T + 1 : Real) : Complex) * Complex.I))).re := by
  apply two_fifths_le_reference_kernel
  · norm_num
  · simp
