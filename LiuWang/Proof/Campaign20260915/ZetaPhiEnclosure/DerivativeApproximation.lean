import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.PhiApproximation

set_option autoImplicit false
noncomputable section

open Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaValidation

def phiTaylor (n : ℕ) (r u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), iteratedDeriv k rsPhi r / k.factorial * u ^ k

theorem rsPhi_taylor_error (n : ℕ) {r x : ℝ} (hr : |r| ≤ 1) (hx : |x| ≤ 1) :
    |rsPhi x - phiTaylor n r (x - r)| ≤
      (derivativeBudget (n + 1) : ℝ) * |x - r| ^ (n + 1) / (n + 1).factorial := by
  by_cases heq : r = x
  · subst x
    simp [phiTaylor, zero_pow_eq]
  have hu : UniqueDiffOn ℝ (uIcc r x) := uniqueDiffOn_Icc (min_lt_max.mpr heq)
  have hdom : ∀ u ∈ uIcc r x, |u| ≤ 1 := by
    intro u hu
    have hr' := abs_le.mp hr
    have hx' := abs_le.mp hx
    exact abs_le.mpr ⟨(le_min hr'.1 hx'.1).trans hu.1, hu.2.trans (max_le hr'.2 hx'.2)⟩
  have hf : ContDiffOn ℝ (n + 1) rsPhi (uIcc r x) := by
    intro u hu
    exact (rsPhi_analytic (by linarith [hdom u hu] : |u| < 3 / 2)).contDiffAt.contDiffWithinAt
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv heq hf
  have ht : taylorWithinEval rsPhi n (uIcc r x) r x = phiTaylor n r (x - r) := by
    rw [taylor_within_apply]
    simp_rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (rsPhi_analytic (by linarith : |r| < 3 / 2)).contDiffAt left_mem_uIcc]
    unfold phiTaylor
    apply Finset.sum_congr rfl
    intro k _
    simp only [smul_eq_mul]
    ring
  rw [ht] at he
  rw [he, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (rsPhi_derivative_bound (n + 1) (hdom y ⟨hy.1.le, hy.2.le⟩))
      (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)

def stencilWeight (n j : ℕ) : ℤ := (-1) ^ (n - j) * (n.choose j : ℤ)

theorem stencilWeight_abs (n j : ℕ) : |(stencilWeight n j : ℝ)| = (n.choose j : ℝ) := by
  simp [stencilWeight, abs_mul, abs_pow]

theorem stencil_polynomial_identity (n : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 6)
    (a : ℕ → ℝ) (h : ℝ) :
    (∑ j ∈ Finset.range (n + 1), (stencilWeight n j : ℝ) *
      ∑ k ∈ Finset.range (n + 1), a k / k.factorial * ((j : ℝ) * h) ^ k) = h ^ n * a n := by
  rcases hn with rfl | rfl | rfl <;>
    norm_num [stencilWeight, Finset.sum_range_succ, Nat.choose] <;> ring

def derivativeApprox (n N : ℕ) (p ep r h d : ℚ) : RationalBall :=
  let b := fun j : ℕ => phiApprox N p ep (r + j * h) 0
  ⟨(∑ j ∈ Finset.range (n + 1), (stencilWeight n j : ℚ) * (b j).center) / h ^ n,
    (∑ j ∈ Finset.range (n + 1), (n.choose j : ℚ) *
      ((b j).radius + (derivativeBudget (n + 1) : ℚ) * |(j : ℚ) * h| ^ (n + 1) /
        (n + 1).factorial)) / |h| ^ n + (derivativeBudget (n + 1) : ℚ) * d⟩

theorem derivativeApprox_correct (n N : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 6)
    (p ep r h d : ℚ) {z : ℝ} (hh : h ≠ 0)
    (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ))
    (hr : |(r : ℝ)| ≤ 1)
    (hdom : ∀ j ∈ Finset.range (n + 1), |((r + j * h : ℚ) : ℝ)| ≤ 1)
    (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (derivativeApprox n N p ep r h d).Contains (iteratedDeriv n rsPhi z) := by
  let b := fun j : ℕ => phiApprox N p ep (r + j * h) 0
  let S : ℝ := ∑ j ∈ Finset.range (n + 1), (stencilWeight n j : ℝ) * ((b j).center : ℝ)
  let E : ℝ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
    (((b j).radius : ℝ) + (derivativeBudget (n + 1) : ℝ) *
      |(j : ℝ) * (h : ℝ)| ^ (n + 1) / (n + 1).factorial)
  have hb (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (b j).Contains (rsPhi ((r + j * h : ℚ) : ℝ)) :=
    phiApprox_correct N p ep (r + j * h) 0 hp (hdom j hj) (hdom j hj) (by simp)
  have ht (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      |rsPhi ((r : ℝ) + j * h) - phiTaylor n r ((j : ℝ) * h)| ≤
        (derivativeBudget (n + 1) : ℝ) * |(j : ℝ) * h| ^ (n + 1) / (n + 1).factorial := by
    have h' := rsPhi_taylor_error n hr (hdom j hj)
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, add_sub_cancel_left] using h'
  have hid : ∑ j ∈ Finset.range (n + 1), (stencilWeight n j : ℝ) *
      phiTaylor n r ((j : ℝ) * h) = (h : ℝ) ^ n * iteratedDeriv n rsPhi r :=
    stencil_polynomial_identity n hn (fun k => iteratedDeriv k rsPhi r) h
  have he : |(h : ℝ) ^ n * iteratedDeriv n rsPhi r - S| ≤ E := by
    rw [← hid]
    dsimp [S, E]
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [← mul_sub, abs_mul, stencilWeight_abs]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 := ht j hj
    have h2 := hb j hj
    simp only [RationalBall.Contains, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at h2
    have h3 := abs_sub_le (phiTaylor n r ((j : ℝ) * h)) (rsPhi ((r : ℝ) + j * h))
      ((b j).center : ℝ)
    rw [abs_sub_comm (phiTaylor _ _ _) (rsPhi _)] at h3
    linarith
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have he' : |iteratedDeriv n rsPhi (r : ℝ) - S / (h : ℝ) ^ n| ≤ E / |(h : ℝ)| ^ n := by
    have heq : iteratedDeriv n rsPhi (r : ℝ) - S / (h : ℝ) ^ n =
        ((h : ℝ) ^ n * iteratedDeriv n rsPhi r - S) / (h : ℝ) ^ n := by
      field_simp
    rw [heq, abs_div, abs_pow]
    exact div_le_div_of_nonneg_right he (pow_nonneg (abs_nonneg _) _)
  have hi := rsPhi_derivative_input_error n hz hr he' hd
  simpa only [derivativeApprox, RationalBall.Contains, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_sum, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast, Rat.cast_intCast, b, S, E] using hi

def derivativeEnclosure (n N : ℕ) (r h d : ℚ) : RationalBall :=
  derivativeApprox n N piApprox piError r h d

theorem derivativeEnclosure_correct (n N : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 6)
    (r h d : ℚ) {z : ℝ} (hh : h ≠ 0) (hr : |(r : ℝ)| ≤ 1)
    (hdom : ∀ j ∈ Finset.range (n + 1), |((r + j * h : ℚ) : ℝ)| ≤ 1)
    (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (derivativeEnclosure n N r h d).Contains (iteratedDeriv n rsPhi z) :=
  derivativeApprox_correct n N hn piApprox piError r h d hh piApprox_correct hr hdom hz hd

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
