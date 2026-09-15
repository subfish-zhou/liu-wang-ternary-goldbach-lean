import LiuWang.Proof.ExplicitPerron.Main

set_option autoImplicit false

noncomputable section

open LiuWang.Proof.ExplicitPerron
open LiuWang.Proof.Interfaces
open scoped BigOperators

example (a : ℕ → ℂ) (A : ℝ → ℝ) (f : ℂ → ℂ)
    (hf : ∀ s : ℂ, 1 < s.re → f s = LSeries a s)
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hA : Monotone A) (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ A n)
    {m : ℕ} (hm : 1 ≤ m) {b c : ℝ} (hb : 1 < b) (hc : 1 ≤ c) :
    ‖(1 / (2 * Real.pi) : ℂ) *
        (∫ u in -c..c,
          f ((b : ℂ) + u * Complex.I) *
            (((m : ℝ) + 1 / 2 : ℂ) ^ ((b : ℂ) + u * Complex.I) /
              ((b : ℂ) + u * Complex.I))) -
        ∑ n ∈ Finset.Icc 1 m, a n‖ ≤
      (((m : ℝ) + 1 / 2) ^ b * (∑' n, ‖LSeries.term a (b : ℂ) n‖) +
        2 ^ b * A ((m : ℝ) + 1 / 2) *
          (((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) + 1 / 2) +
            3 / 2 * ((m : ℝ) + 1 / 2) - 1 / 2) +
        ((m : ℝ) + 1 / 2) * A (2 * ((m : ℝ) + 1 / 2)) *
          (Real.log ((m : ℝ) + 1 / 2) + Real.log 2 + 2)) /
        (Real.pi * c * Real.log 2) :=
  source_perron_of_series a A f hf hsum hA ha hm hb hc

example {N q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hN : Real.exp 2000 ≤ (N : ℝ)) (_hq : 1 ≤ q) (_hqUpper : (q : ℝ) ≤ (Real.log N) ^ 6)
    {t Hminus Hplus : ℝ} (ht : (N : ℝ) / 1000 ≤ t) (_htUpper : t ≤ N)
    (hminus : |Hminus + (Real.log N) ^ 15| ≤ 1)
    (hplus : |Hplus - (Real.log N) ^ 15| ≤ 1) :
    ‖(1 / (2 * Real.pi) : ℂ) *
        (∫ u in Hminus..Hplus,
          (-logDeriv chi.LFunction ((1 + 1 / Real.log N : ℂ) + u * Complex.I)) *
            ((t : ℂ) ^ ((1 + 1 / Real.log N : ℂ) + u * Complex.I) -
              (2.5 : ℂ) ^ ((1 + 1 / Real.log N : ℂ) + u * Complex.I)) /
            ((1 + 1 / Real.log N : ℂ) + u * Complex.I)) -
        ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n‖ ≤
      closedRealEndpointError t (1 + 1 / Real.log N) ((Real.log N) ^ 15) Hminus Hplus := by
  have h := sourceDomain_right_perron chi hN ht hminus hplus
  norm_num only [vertical, centeredIntegrand, psi_eq_sum, sourceWindowLower, sourceL, sourceT,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div,
    show (5 / 2 : ℂ) = 2.5 by norm_num] at h ⊢
  exact h

example {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t Hminus Hplus : ℝ} (ht : sourceWindowLower N ≤ t)
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    ‖vertical (centeredIntegrand (1 : DirichletCharacter ℂ 1) t (5 / 2))
        (1 + 1 / sourceL N) Hminus Hplus - psi (1 : DirichletCharacter ℂ 1) t‖ ≤
      closedRealEndpointError t (1 + 1 / sourceL N) (sourceT N) Hminus Hplus :=
  sourceDomain_right_perron 1 hN ht hminus hplus
