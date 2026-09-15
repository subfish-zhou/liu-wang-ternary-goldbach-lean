import LiuWang.Proof.Campaign20260915.ZetaValidation.HighOrderEvaluation
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem normalizedBernoulli_has_unit_zero (k : ℕ) (hk : 1 ≤ k) :
    ∃ c ∈ Ioo (0 : ℝ) 1, normalizedBernoulli k c = 0 :=
  exists_hasDerivAt_eq_zero (by norm_num)
    (continuous_normalizedBernoulli (k + 1)).continuousOn
    (normalizedBernoulli_one (k + 1) (by omega)).symm
    (fun x _ => hasDerivAt_normalizedBernoulli k x)

theorem abs_normalizedBernoulli_uniform (k : ℕ) (hk : 1 ≤ k)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    |normalizedBernoulli k x| ≤ 1 / 2 := by
  induction k, hk using Nat.le_induction generalizing x with
  | base =>
      rw [normalizedBernoulli_first, abs_le]
      constructor <;> linarith [hx.1, hx.2]
  | succ k hk ih =>
      obtain ⟨c, hc, hzero⟩ := normalizedBernoulli_has_unit_zero (k + 1) (by omega)
      have hd : ∀ u ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (normalizedBernoulli (k + 1)) u :=
        fun u _ => (hasDerivAt_normalizedBernoulli k u).differentiableAt
      have hb : ∀ u ∈ Icc (0 : ℝ) 1, ‖deriv (normalizedBernoulli (k + 1)) u‖ ≤ 1 / 2 := by
        intro u hu
        rw [(hasDerivAt_normalizedBernoulli k u).deriv, Real.norm_eq_abs]
        exact ih hu
      have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc 0 1)
        (show c ∈ Icc (0 : ℝ) 1 from ⟨hc.1.le, hc.2.le⟩) hx
      rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hm
      have hdist : |x - c| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2, hc.1, hc.2]
      linarith

theorem norm_bernoulliTail_uniform (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re + k)
    {a : ℝ} (ha : 0 < a) :
    ‖∫ u in Ioi a, bernoulliKernel k s u‖ ≤
      a ^ (1 - s.re - k) / (2 * (s.re + k - 1)) := by
  have hp {u : ℝ} (hu : 0 < u) :
      ‖bernoulliKernel k s u‖ ≤ (1 / 2 : ℝ) * u ^ (-s.re - k) := by
    rw [bernoulliKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp only [sub_re, neg_re, natCast_re]
    exact mul_le_mul_of_nonneg_right
      (abs_normalizedBernoulli_uniform k hk ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩)
      (Real.rpow_nonneg hu.le _)
  calc
    _ ≤ ∫ u in Ioi a, (1 / 2 : ℝ) * u ^ (-s.re - k) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - k < -1) ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hp (ha.trans hu)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
      rw [show -s.re - (k : ℝ) + 1 = -(s.re + k - 1) by ring, neg_div_neg_eq,
        show -(s.re + (k : ℝ) - 1) = 1 - s.re - k by ring]
      field_simp

theorem eulerMaclaurin_half_kernel_error (m : ℕ) {s : ℂ} (hs : 1 / 10 < s.re)
    (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - eulerMaclaurinApprox s N m‖ ≤
      (‖s‖ + m) ^ (m + 1) * (N : ℝ) ^ (-s.re - m) / (2 * (s.re + m)) := by
  rw [zeta_sub_eulerMaclaurinApprox m hs hs1 hN, norm_mul, norm_neg]
  have hb := norm_bernoulliTail_uniform (m + 1) (by omega) (s := s)
    (by push_cast; linarith : 1 < s.re + (m + 1 : ℕ))
    (a := N) (by exact_mod_cast (show 0 < N by omega))
  push_cast at hb
  rw [show (1 : ℝ) - s.re - ((m : ℝ) + 1) = -s.re - m by ring,
    show s.re + ((m : ℝ) + 1) - 1 = s.re + m by ring] at hb
  have hp : 0 ≤ (N : ℝ) ^ (-s.re - m) / (2 * (s.re + m)) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (by linarith [Nat.cast_nonneg m (α := ℝ)])
  simpa only [mul_div_assoc] using
    mul_le_mul (norm_risingProduct_le s m) hb (norm_nonneg _) (by positivity)

theorem eulerMaclaurin_geometric_error (m : ℕ) {s : ℂ} (hs : 1 / 10 < s.re)
    (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) (hscale : ‖s‖ + m ≤ (N : ℝ) / 2) :
    ‖riemannZeta s - eulerMaclaurinApprox s N m‖ ≤
      (N : ℝ) ^ (1 - s.re) / ((2 : ℝ) ^ (m + 2) * (s.re + m)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : 0 < s.re + m := by linarith [Nat.cast_nonneg m (α := ℝ)]
  have he := eulerMaclaurin_half_kernel_error m hs hs1 hN
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ‖s‖ + m) hscale (m + 1)
  have hpow : (N : ℝ) ^ (m + 1) * (N : ℝ) ^ (-s.re - m) =
      (N : ℝ) ^ (1 - s.re) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNp]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ((N : ℝ) / 2) ^ (m + 1) * (N : ℝ) ^ (-s.re - m) /
        (2 * (s.re + m)) :=
      he.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hNp.le _)) (by positivity))
    _ = _ := by
      rw [div_pow]
      rw [div_mul_eq_mul_div, hpow]
      rw [show (m + 2 : ℕ) = (m + 1) + 1 by omega, pow_succ]
      field_simp
      ring

#print axioms abs_normalizedBernoulli_uniform
#print axioms eulerMaclaurin_geometric_error

end LiuWang.Proof.Campaign20260915.ZetaValidation
