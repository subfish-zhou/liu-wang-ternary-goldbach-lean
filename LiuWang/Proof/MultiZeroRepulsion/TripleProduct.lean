import LiuWang.Proof.MultiZeroRepulsion.EulerProduct

/-! The four conjugation choices in the source three-character Euler product. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.MultiZeroRepulsion

def tripleCharacters {q : ℕ} (chi psi eta : DirichletCharacter ℂ q) :
    Fin 14 → DirichletCharacter ℂ q :=
  ![1, chi, psi, eta, chi * psi, chi * psi⁻¹, chi * eta, chi * eta⁻¹,
    psi * eta, psi * eta⁻¹, chi * psi * eta, chi * psi⁻¹ * eta,
    chi * psi * eta⁻¹, chi * psi⁻¹ * eta⁻¹]

def tripleHeights (t u v : ℝ) : Fin 14 → ℝ :=
  ![0, t, u, v, t + u, t - u, t + v, t - v, u + v, u - v,
    t + u + v, t - u + v, t + u - v, t - u - v]

def tripleCoefficients : Fin 14 → ℝ := ![4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1]

theorem triple_phase_nonneg {q n : ℕ} (chi psi eta : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) (t u v : ℝ) :
    0 ≤ ∑ j : Fin 14, tripleCoefficients j *
      (phase (tripleCharacters chi psi eta j) (tripleHeights t u v j) n).re := by
  have hchi := (neg_le_abs (phase chi t n).re).trans (abs_re_le_norm _)
  have hpsi := (neg_le_abs (phase psi u n).re).trans (abs_re_le_norm _)
  have heta := (neg_le_abs (phase eta v n).re).trans (abs_re_le_norm _)
  rw [phase_norm chi hn hu] at hchi
  rw [phase_norm psi hn hu] at hpsi
  rw [phase_norm eta hn hu] at heta
  have he : (∑ j : Fin 14, tripleCoefficients j *
      (phase (tripleCharacters chi psi eta j) (tripleHeights t u v j) n).re) =
      4 * (1 + (phase chi t n).re) * (1 + (phase psi u n).re) *
        (1 + (phase eta v n).re) := by
    simp only [Fin.sum_univ_succ, tripleCharacters, tripleHeights, tripleCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    simp only [sub_eq_add_neg, phase_one hu, phase_mul _ _ hn, phase_inv,
      one_re, mul_re, mul_im, conj_re, conj_im]
    ring
  rw [he]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
    (by linarith)) (by linarith)

theorem triple_euler_nonneg {q : ℕ} [NeZero q] (chi psi eta : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    0 ≤ ∑ j : Fin 14, tripleCoefficients j *
      dampedLogDeriv (tripleCharacters chi psi eta j) sigma (stechkinSigma sigma) stechkinK
        (tripleHeights t u v j) :=
  damped_polynomial_nonneg Finset.univ (tripleCharacters chi psi eta) (tripleHeights t u v)
    tripleCoefficients (fun _n hn hu => triple_phase_nonneg chi psi eta hn hu t u v)
    hs (stechkinSigma_ge hs) stechkinK_mem

end LiuWang.Proof.MultiZeroRepulsion
