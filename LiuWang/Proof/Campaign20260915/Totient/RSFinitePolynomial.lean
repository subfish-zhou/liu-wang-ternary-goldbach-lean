import LiuWang.Proof.Campaign20260915.Totient.RSMainDifference
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Polynomial Finset MeasureTheory

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPolyIntegral (P : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ range (P.natDegree + 1), monomial (k + 1) (P.coeff k / (k + 1))

theorem rsPolyIntegral_derivative (P : ℂ[X]) :
    (rsPolyIntegral P).derivative = P := by
  unfold rsPolyIntegral
  rw [derivative_sum]
  conv_rhs => rw [P.as_sum_range]
  apply sum_congr rfl
  intro k _
  rw [derivative_monomial]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  congr 1
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  field_simp

theorem rsPolyIntegral_degree (P : ℂ[X]) :
    (rsPolyIntegral P).natDegree ≤ P.natDegree + 1 := by
  apply (natDegree_sum_le _ _).trans
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun k hk => ?_⟩
  exact (natDegree_monomial_le _).trans (by have := mem_range.mp hk; omega)

theorem rsPolyIntegral_interval (P : ℂ[X]) (a b : ℝ) :
    (∫ t in a..b, P.eval (t : ℂ)) =
      (rsPolyIntegral P).eval (b : ℂ) - (rsPolyIntegral P).eval (a : ℂ) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    simpa only [rsPolyIntegral_derivative] using
      ((rsPolyIntegral P).hasDerivAt (t : ℂ)).comp_ofReal
  · exact (P.differentiable.continuous.comp Complex.continuous_ofReal).intervalIntegrable a b

theorem rsPolynomial_difference_vanish {P : ℂ[X]} {m : ℕ}
    (hP : P.natDegree < m) (h x : ℝ) :
    (fwdDiff h)^[m] (fun t => P.eval (t : ℂ)) x = 0 := by
  let Q := P.comp (C (x : ℂ) + C (h : ℂ) * X)
  have hQ : Q.natDegree < m := by
    have hl : (C (x : ℂ) + C (h : ℂ) * X).natDegree ≤ 1 := by
      exact natDegree_add_le_of_degree_le (by simp)
        ((natDegree_mul_le).trans (by simp))
    exact (natDegree_comp_le.trans (Nat.mul_le_mul_left _ hl)).trans_lt (by simpa using hP)
  have hz := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQ) (0 : ℂ)
  simp only [Pi.zero_apply] at hz
  rw [fwdDiff_iter_eq_sum_shift] at hz ⊢
  convert hz using 1
  apply sum_congr rfl
  intro k _
  congr 1
  simp only [Q, eval_comp, eval_add, eval_mul, eval_C, eval_X, zero_add,
    nsmul_eq_mul, mul_one, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [mul_comm (h : ℂ)]

#print axioms rsPolyIntegral_derivative
#print axioms rsPolyIntegral_degree
#print axioms rsPolyIntegral_interval
#print axioms rsPolynomial_difference_vanish

end LiuWang.Proof.Campaign20260915.Totient
