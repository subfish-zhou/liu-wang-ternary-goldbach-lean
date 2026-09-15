import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelSaddleTaylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
noncomputable section
open Complex
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

private theorem monomial_product_derivative (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (p n : ℕ) :
    iteratedDeriv n (fun z => z ^ p * f z) 0 =
      (n.choose p : ℂ) * p.factorial * iteratedDeriv (n - p) f 0 := by
  have h := iteratedDeriv_mul (n := n) (x := (0 : ℂ))
    (f := fun z : ℂ => z ^ p) (g := f) (by fun_prop) hf.contDiffAt
  change iteratedDeriv n (fun z : ℂ => z ^ p * f z) 0 = _ at h
  rw [h]
  have hz (j : ℕ) (hj : j ≠ p) : iteratedDeriv j (fun z : ℂ => z ^ p) 0 = 0 := by
    rw [iteratedDeriv_pow]
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [zero_pow (Nat.sub_ne_zero_of_lt hj), mul_zero]
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hj, Nat.cast_zero, zero_mul]
  rw [Finset.sum_eq_single p]
  · simp [iteratedDeriv_pow, Nat.descFactorial_self]
  · intro j _ hj
    rw [hz j hj, mul_zero, zero_mul]
  · intro hp
    have hn : n < p := by
      simp only [Finset.mem_range, not_lt] at hp
      omega
    rw [Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, zero_mul, zero_mul]

private theorem saddle_derivative_relation (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (n : ℕ) :
    (lambda : ℂ) * iteratedDeriv (n + 1) (rsSaddleWeight sigma lambda) 0 =
      ((sigma - 1 : ℝ) : ℂ) * iteratedDeriv n (rsSaddleWeight sigma lambda) 0 -
        (n : ℂ) * iteratedDeriv n (rsSaddleWeight sigma lambda) 0 +
          I * ((n.choose 2 : ℂ) * 2 * iteratedDeriv (n - 2) (rsSaddleWeight sigma lambda) 0) := by
  let f := rsSaddleWeight sigma lambda
  have hf : AnalyticAt ℂ f 0 := rsSaddle_analytic sigma hl (by simpa)
  have he : (fun z : ℂ => (lambda : ℂ) * deriv f z) =ᶠ[nhds 0]
      fun z => ((sigma - 1 : ℝ) : ℂ) * f z - z * deriv f z + I * (z ^ 2 * f z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hl] with z hz
    have h := rsSaddle_differential_equation sigma hl (by simpa using hz : ‖z‖ < lambda)
    dsimp [f]
    push_cast at h ⊢
    linear_combination h
  have hd := he.iteratedDeriv_eq n
  have ha : AnalyticAt ℂ (fun z : ℂ => ((sigma - 1 : ℝ) : ℂ) * f z - z * deriv f z) 0 :=
    (analyticAt_const.mul hf).sub (analyticAt_id.mul hf.deriv)
  have hb : AnalyticAt ℂ (fun z : ℂ => I * (z ^ 2 * f z)) 0 :=
    analyticAt_const.mul ((analyticAt_id.pow 2).mul hf)
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add ha.contDiffAt hb.contDiffAt,
    iteratedDeriv_fun_sub (f := fun z : ℂ => ((sigma - 1 : ℝ) : ℂ) * f z)
      (g := fun z : ℂ => z * deriv f z) (analyticAt_const.mul hf).contDiffAt
      (analyticAt_id.mul hf.deriv).contDiffAt,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    ← iteratedDeriv_succ'] at hd
  have hx := monomial_product_derivative (deriv f) hf.deriv 1 n
  have hx2 := monomial_product_derivative f hf 2 n
  norm_num only [pow_one, Nat.factorial_one, Nat.factorial_two, mul_one, Nat.choose_one_right] at hx hx2
  rw [hx, hx2] at hd
  by_cases hn : n = 0
  · subst n
    simpa [f] using hd
  · have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
    rw [← iteratedDeriv_succ', hsucc] at hd
    exact hd

theorem rsSaddle_coefficient_two (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    rsSaddleCoefficient sigma lambda 2 =
      (((sigma - 1) * (sigma - 2) : ℝ) : ℂ) / (2 * (lambda : ℂ) ^ 2) := by
  have h := saddle_derivative_relation sigma hl 1
  norm_num only [Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2), Nat.cast_zero,
    zero_mul, mul_zero, Nat.cast_one, one_mul, iteratedDeriv_one, add_zero] at h
  rw [rsSaddle_first_deriv sigma hl] at h
  have hl0 : (lambda : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
  unfold rsSaddleCoefficient
  norm_num only [Nat.factorial_two]
  push_cast at h ⊢
  field_simp at h ⊢
  linear_combination h

theorem rsSaddle_coefficient_recurrence (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (n : ℕ) :
    ((n + 3 : ℕ) : ℂ) * lambda * rsSaddleCoefficient sigma lambda (n + 3) =
      -(((n + 3 : ℕ) : ℂ) - sigma) * rsSaddleCoefficient sigma lambda (n + 2) +
        I * rsSaddleCoefficient sigma lambda n := by
  have h := saddle_derivative_relation sigma hl (n + 2)
  have hfac : ((n + 2).choose 2 : ℂ) * 2 * (n.factorial : ℂ) = (n + 2).factorial := by
    have he := Nat.choose_mul_factorial_mul_factorial (show 2 ≤ n + 2 by omega)
    norm_num only [Nat.add_sub_cancel, Nat.factorial_two] at he
    exact_mod_cast he
  have hn3 : ((n + 3 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 3 ≠ 0 by omega)
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn2 : ((n + 2).factorial : ℂ) ≠ 0 := by exact_mod_cast (n + 2).factorial_ne_zero
  have hf3 : ((n + 3).factorial : ℂ) = ((n + 3 : ℕ) : ℂ) * ((n + 2).factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ (n + 2)
  unfold rsSaddleCoefficient
  rw [hf3]
  field_simp
  norm_num only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd] at h
  push_cast at h hfac ⊢
  linear_combination (n.factorial : ℂ) * h + I *
    iteratedDeriv n (rsSaddleWeight sigma lambda) 0 * hfac

end LiuWang.Proof.Campaign20260915.ZetaValidation
