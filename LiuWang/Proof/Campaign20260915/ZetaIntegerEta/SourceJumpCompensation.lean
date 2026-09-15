import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.SourceRemainderLimits

set_option autoImplicit false
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem localPrefactor_integer_independent (sigma : ℝ) (k m n : ℕ) :
    rsLocalPrefactor sigma k m = rsLocalPrefactor sigma k n := by
  have he (j : ℕ) : exp (-2 * Real.pi * I * j * ((k : ℝ) : ℂ)) = 1 := by
    rw [show -2 * Real.pi * I * j * ((k : ℝ) : ℂ) =
      -(((j * k : ℕ) : ℂ) * (2 * Real.pi * I)) by push_cast; ring,
      exp_neg, exp_nat_mul_two_pi_mul_I, inv_one]
  unfold rsLocalPrefactor
  rw [he m, he n]

theorem sourceZetaPolynomialRemainder_endpoint_jump (sigma : ℝ) (n N : ℕ) :
    let x : ℝ := (n : ℝ) + 1
    let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * x : ℝ) : ℂ) ^ 2
    sourceZetaPolynomialRemainder sigma x (n + 1) N -
      sourceZetaPolynomialRemainder sigma x n N =
      -(1 / (n + 1 : ℂ) ^ s +
        (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
          (n + 1 : ℂ) ^ (s - 1)) -
      rsHankelPrefactor s * rsLocalPrefactor sigma x (n + 1) *
        (sourceGaussianPhase x (n + 1) *
          ∑ k ∈ Finset.range N, ((-1 : ℂ) ^ k + 1) *
            (rsSaddleCoefficient sigma (rsSaddleScale * x) k *
              (rsSaddleScale : ℂ) ^ k * correctionMoment k 1)) := by
  dsimp only
  have hp : rsLocalPrefactor sigma ((n : ℝ) + 1) n =
      rsLocalPrefactor sigma ((n : ℝ) + 1) (n + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      localPrefactor_integer_independent sigma (n + 1) n (n + 1)
  have hl : sourcePhiParameter ((n : ℝ) + 1) n = 1 := by
    unfold sourcePhiParameter
    ring
  have hr : sourcePhiParameter ((n : ℝ) + 1) (n + 1) = -1 := by
    simp [sourcePhiParameter]
  simp only [sourceZetaPolynomialRemainder, hl, hr, ofReal_neg, ofReal_one, hp]
  linear_combination
    -(sourceFiniteSums_succ
      ((sigma : ℂ) + I * ((rsSaddleScale * ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) n) -
    rsHankelPrefactor
      ((sigma : ℂ) + I * ((rsSaddleScale * ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
      rsLocalPrefactor sigma ((n : ℝ) + 1) (n + 1) *
        (sourcePolynomial_endpoint_jump sigma n N)

theorem actual_C2_zeta_formula_tendsto_right (sigma : ℝ) (hs : sigma ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun eta : ℝ =>
      let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
      sourceFiniteSums s ⌊eta⌋₊ + rsHankelPrefactor s * rsSourceC2 s eta ⌊eta⌋₊)
      (𝓝[>] (n : ℝ))
      (𝓝 (riemannZeta ((sigma : ℂ) + I * ((rsSaddleScale * (n : ℝ) : ℝ) : ℂ) ^ 2))) := by
  let s : ℝ → ℂ := fun eta => (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
  have ht : 0 < (s n).im := by
    simpa only [s, ← ofReal_pow, add_im, ofReal_im, mul_im, I_re, I_im,
      zero_mul, one_mul, zero_add, ofReal_re] using
        sq_pos_of_pos (mul_pos rsSaddleScale_pos (show (0 : ℝ) < n by exact_mod_cast hn))
  have hc := actual_C2_polynomial_remainder_tendsto_right sigma hs hn 0
  simp only [rsLocalPolynomialIntegrand, Finset.sum_range_zero, mul_zero, integral_zero,
    add_zero, sourceZetaPolynomialRemainder, sub_zero] at hc
  have hm := (sourceFiniteSums_tendsto_right n
    (s := s) (by dsimp [s]; fun_prop) ht).mono_left
      (nhdsWithin_mono _ (show Ioi (n : ℝ) ⊆ Ici (n : ℝ) by
        intro x hx
        simp only [mem_Ioi, mem_Ici] at hx ⊢
        exact hx.le))
  simpa only [s, add_sub_cancel] using hm.add hc

#print axioms localPrefactor_integer_independent
#print axioms sourceZetaPolynomialRemainder_endpoint_jump
#print axioms actual_C2_zeta_formula_tendsto_right

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
