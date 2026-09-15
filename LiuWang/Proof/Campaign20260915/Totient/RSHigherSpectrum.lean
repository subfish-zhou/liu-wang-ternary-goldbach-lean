import LiuWang.Proof.Campaign20260915.Totient.RSFinitePolynomial
import LiuWang.Proof.Campaign20260915.Totient.RSGammaRecursion

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Polynomial MeasureTheory Set
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPolePrimitive (m : ℕ) (x : ℝ) : ℝ :=
  rsMainPrimitive m x - Real.log (2 * Real.pi) * x ^ m / m.factorial

theorem rsPolePrimitive_deriv (m : ℕ) (x : ℝ) :
    HasDerivAt (rsPolePrimitive (m + 1)) (rsPolePrimitive m x) x := by
  have hd := (rsMainPrimitive_deriv m x).sub
    (((hasDerivAt_pow (m + 1) x).const_mul (Real.log (2 * Real.pi))).div_const
      ((m + 1).factorial : ℝ))
  convert! hd using 1
  unfold rsPolePrimitive
  rw [Nat.factorial_succ]
  push_cast
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem rsPolePrimitive_integral (m : ℕ) (a b : ℝ) :
    (∫ t in a..b, (rsPolePrimitive m t : ℂ)) =
      (rsPolePrimitive (m + 1) b : ℂ) - (rsPolePrimitive (m + 1) a : ℂ) := by
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => rsPolePrimitive_deriv m t) (by
      apply Continuous.intervalIntegrable
      unfold rsPolePrimitive rsMainPrimitive
      fun_prop)]
  exact Complex.ofReal_sub _ _

private theorem zero_integral_two {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 1 < x) :
    (∫ t in (2 : ℝ)..x, ∑' p, rsZeroPrimitive m t p) =
      (∑' p, rsZeroPrimitive (m + 1) x p) - ∑' p, rsZeroPrimitive (m + 1) 2 p := by
  rcases le_total 2 x with h | h
  · exact rsZeroSum_integral hm (by norm_num) h
  · rw [intervalIntegral.integral_symm,
      rsZeroSum_integral hm hx.le h]
    abel

private theorem psi_integral_two (m : ℕ) (x : ℝ) :
    (∫ t in (2 : ℝ)..x, (rsPsiPrimitive m t : ℂ)) =
      (rsPsiPrimitive (m + 1) x : ℂ) - (rsPsiPrimitive (m + 1) 2 : ℂ) := by
  rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_sub]
  congr 1
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (rsPsiPrimitive_integrable m 0 2) (rsPsiPrimitive_integrable m 2 x)
  change _ = (∫ t in (0 : ℝ)..x, rsPsiPrimitive m t) -
    ∫ t in (0 : ℝ)..2, rsPsiPrimitive m t
  linarith

theorem rsPsiPrimitive_spectral_polynomial {m : ℕ} (hm : 1 ≤ m) :
    ∃ P : ℂ[X], P.natDegree < m ∧ ∀ x : ℝ, 1 < x →
      (rsPsiPrimitive m x : ℂ) =
        (rsPolePrimitive m x : ℂ) - (∑' p, rsZeroPrimitive m x p) +
          rsGammaPrimitive m x + P.eval (x : ℂ) := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨C ((Real.log (2 * Real.pi) : ℂ) - 1 / 2 +
      ∑' p, rsZeroPrimitive 1 1 p), by simp, ?_⟩
    intro x hx
    rw [rsPsiPrimitive_one_spectral hx]
    simp only [rsPolePrimitive, rsMainPrimitive, rsGammaPrimitive, eval_C]
    norm_num
    ring
  | succ m hm ih =>
    obtain ⟨P, hP, he⟩ := ih
    let c : ℂ := (rsPsiPrimitive (m + 1) 2 : ℂ) -
      (rsPolePrimitive (m + 1) 2 : ℂ) +
      (∑' p, rsZeroPrimitive (m + 1) 2 p) - (rsPolyIntegral P).eval 2
    refine ⟨rsPolyIntegral P + C c, ?_, ?_⟩
    · exact (natDegree_add_le_of_degree_le (rsPolyIntegral_degree P)
        (by simp)).trans_lt (by omega)
    intro x hx
    have hmem (t : ℝ) (ht : t ∈ uIcc 2 x) : 1 < t := by
      exact (lt_min (by norm_num) hx).trans_le ht.1
    have hp : IntervalIntegrable (fun t => (rsPolePrimitive m t : ℂ)) volume 2 x := by
      apply Continuous.intervalIntegrable
      unfold rsPolePrimitive rsMainPrimitive
      fun_prop
    have hz : IntervalIntegrable (fun t => ∑' p, rsZeroPrimitive m t p) volume 2 x := by
      apply ContinuousOn.intervalIntegrable
      exact rsZeroSum_continuousOn_Icc hm (le_min (by norm_num) hx.le)
    have hg := rsGammaPrimitive_integrable m (by norm_num : (1 : ℝ) < 2) hx
    have hpol : IntervalIntegrable (fun t : ℝ => P.eval (t : ℂ)) volume 2 x :=
      (P.differentiable.continuous.comp Complex.continuous_ofReal).intervalIntegrable 2 x
    have hi := intervalIntegral.integral_congr (μ := volume)
      (fun t ht => he t (hmem t ht))
    rw [psi_integral_two,
      intervalIntegral.integral_add ((hp.sub hz).add hg) hpol,
      intervalIntegral.integral_add (hp.sub hz) hg,
      intervalIntegral.integral_sub hp hz, rsPolePrimitive_integral,
      zero_integral_two hm hx, rsGammaPrimitive_integral hm, rsPolyIntegral_interval] at hi
    simp only [eval_add, eval_C]
    dsimp [c]
    linear_combination hi

theorem rsPsiPrimitive_spectral_difference {m : ℕ} (hm : 1 ≤ m)
    {h x : ℝ} (hh : 0 ≤ h) (hx : 1 < x) :
    (fwdDiff h)^[m] (fun t => (rsPsiPrimitive m t : ℂ)) x =
      (fwdDiff h)^[m] (fun t => (rsPolePrimitive m t : ℂ) -
        (∑' p, rsZeroPrimitive m t p) + rsGammaPrimitive m t) x := by
  obtain ⟨P, hP, he⟩ := rsPsiPrimitive_spectral_polynomial hm
  have hlocal :
      (fwdDiff h)^[m] (fun t => (rsPsiPrimitive m t : ℂ)) x =
        (fwdDiff h)^[m] ((fun t => (rsPolePrimitive m t : ℂ) -
          (∑' p, rsZeroPrimitive m t p) + rsGammaPrimitive m t) +
          fun t : ℝ => P.eval (t : ℂ)) x := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    exact he (x + k • h) (by
      have hk : 0 ≤ k • h := nsmul_nonneg hh k
      linarith)
  rw [hlocal, fwdDiff_iter_add]
  change _ = _
  rw [Pi.add_apply, rsPolynomial_difference_vanish hP, add_zero]

#print axioms rsPolePrimitive_deriv
#print axioms rsPolePrimitive_integral
#print axioms rsPsiPrimitive_spectral_polynomial
#print axioms rsPsiPrimitive_spectral_difference

end LiuWang.Proof.Campaign20260915.Totient
