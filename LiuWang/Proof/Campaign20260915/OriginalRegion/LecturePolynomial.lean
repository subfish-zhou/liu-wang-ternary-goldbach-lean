import LiuWang.Proof.Campaign20260915.OriginalRegion.SignedEnvelope

/-! Exact algebra for the polynomial in Kadiri's BIRS notes, not a JNT source certificate. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators Classical
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

def squareCoefficients (a b : ℝ) : Fin 5 → ℝ :=
  ![3 + 4 * (a ^ 2 + 4 * a * b + b ^ 2) + 8 * a ^ 2 * b ^ 2,
    4 * (a + b) * (3 + 4 * a * b),
    4 + 4 * (a ^ 2 + 4 * a * b + b ^ 2), 4 * (a + b), 1]

def lectureCoefficients : Fin 5 → ℝ := squareCoefficients 0.9126 0.2766

theorem lectureCoefficients_exact :
    lectureCoefficients =
      ![11.1859355312082048, 19.073344004352, 11.67618784, 4.7568, 1] := by
  ext j
  fin_cases j <;> norm_num [lectureCoefficients, squareCoefficients]

theorem square_polynomial_identity (a b : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : Fin 5, squareCoefficients a b j * (z ^ (j : ℕ)).re) =
      8 * (z.re + a) ^ 2 * (z.re + b) ^ 2 := by
  have hy : z.im ^ 2 = 1 - z.re ^ 2 := by
    have hh := Complex.normSq_eq_norm_sq z
    rw [hz] at hh
    simp only [Complex.normSq_apply] at hh
    nlinarith
  simp only [Fin.sum_univ_succ, squareCoefficients, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ]
  norm_num [pow_succ, mul_re, mul_im, add_re]
  ring_nf
  rw [show z.im ^ 4 = (z.im ^ 2) ^ 2 by ring, hy]
  ring

theorem square_polynomial_nonneg (a b : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ ∑ j : Fin 5, squareCoefficients a b j * (z ^ (j : ℕ)).re := by
  rw [square_polynomial_identity a b hz]
  positivity

theorem lectureCoefficients_pos (j : Fin 5) : 0 < lectureCoefficients j := by
  rw [lectureCoefficients_exact]
  fin_cases j <;> norm_num

theorem phase_nat_power {q n : ℕ} (chi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) (t : ℝ) (k : ℕ) :
    phase (chi ^ k) ((k : ℝ) * t) n = phase chi t n ^ k := by
  induction k with
  | zero => simp [phase_one hu]
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul, phase_mul _ _ hn, ih, pow_succ]

theorem lecture_phase_nonneg {q n : ℕ} (chi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) (t : ℝ) :
    0 ≤ ∑ j : Fin 5, lectureCoefficients j *
      (phase (chi ^ (j : ℕ)) ((j : ℝ) * t) n).re := by
  simp only [phase_nat_power chi hn hu]
  exact square_polynomial_nonneg _ _ (phase_norm chi hn hu t)

theorem lecture_selected_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) (v : Fin 5 → Finset ℂ)
    (hr : ∀ j, ∀ rho ∈ v j, 1 / 2 < rho.re ∧ rho.re < 1) :
    (∑ j : Fin 5, lectureCoefficients j *
      ordinaryMass (chi ^ (j : ℕ)) sigma ((j : ℝ) * t) (v j)) ≤
    ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * t) :=
  signed_polynomial_selected_bound Finset.univ _ _ _ (fun j _ => (lectureCoefficients_pos j).le)
    (fun _ hn hu => lecture_phase_nonneg chi hn hu t) hs v (fun j _ => hr j)

theorem lecture_selected_envelope_strict {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (t : ℝ) (v : Fin 5 → Finset ℂ)
    (hr : ∀ j, ∀ rho ∈ v j, 1 / 2 < rho.re ∧ rho.re < 1) :
    (∑ j : Fin 5, lectureCoefficients j *
      ordinaryMass (chi ^ (j : ℕ)) sigma ((j : ℝ) * t) (v j)) <
    ∑ j : Fin 5, lectureCoefficients j *
      signedEnvelope (chi ^ (j : ℕ)) sigma ((j : ℝ) * t) := by
  apply (lecture_selected_bound chi hs.1 t v hr).trans_lt
  apply Finset.sum_lt_sum
  · intro j _
    exact mul_le_mul_of_nonneg_left (signedCost_le_envelope _ hs _) (lectureCoefficients_pos j).le
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, pow_zero] using
      mul_lt_mul_of_pos_left (signed_principal_envelope_strict (q := q) hs 0)
        (lectureCoefficients_pos 0)

end LiuWang.Proof.Campaign20260915.OriginalRegion
