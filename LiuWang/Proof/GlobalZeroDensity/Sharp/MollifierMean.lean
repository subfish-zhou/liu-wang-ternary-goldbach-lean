import LiuWang.Proof.GlobalZeroDensity.Sharp.FiniteMean

/-! The strict-cutoff mollifier as an actual finite exponential sum. -/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

def criticalCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)

theorem critical_term_wave {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I) =
      criticalCoefficient n * wave (-Real.log n) t := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [Complex.cpow_add _ _ hn0]
  have he : ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ = wave (-Real.log n) t := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_neg]
    unfold wave
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  simp only [criticalCoefficient, div_eq_mul_inv, mul_inv_rev, he]
  ring

theorem Q_eq_exponential (y t : ℝ) :
    Q y ((1 / 2 : ℂ) + t * Complex.I) =
      exponentialPolynomial ((range ⌈y⌉₊).erase 0) criticalCoefficient
        (fun n => -Real.log n) t := by
  unfold Q exponentialPolynomial
  have hs : (∑ n ∈ (range ⌈y⌉₊).erase 0,
      (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I)) =
      ∑ n ∈ range ⌈y⌉₊,
      (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I) := by
    apply sum_subset (erase_subset _ _)
    intro n hn hn'
    have : n = 0 := by simpa only [mem_erase, hn, and_true, not_not] using hn'
    subst n
    simp
  rw [← hs]
  apply sum_congr rfl
  intro n hn
  exact critical_term_wave (Nat.pos_of_ne_zero (mem_erase.mp hn).1) t

theorem norm_criticalCoefficient {n : ℕ} (hn : 0 < n) :
    ‖criticalCoefficient n‖ = |(ArithmeticFunction.moebius n : ℝ)| / Real.sqrt n := by
  rw [criticalCoefficient, norm_div, Complex.norm_natCast_cpow_of_pos hn]
  rw [show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num]
  rw [← Real.sqrt_eq_rpow]
  congr 1
  exact_mod_cast Complex.norm_intCast (ArithmeticFunction.moebius n)

theorem criticalCoefficient_sq {n : ℕ} (hn : 0 < n) :
    ‖criticalCoefficient n‖ ^ 2 = (ArithmeticFunction.moebius n : ℝ) ^ 2 / n := by
  rw [norm_criticalCoefficient hn, div_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem negative_log_inj (N : ℕ) :
    Set.InjOn (fun n : ℕ => -Real.log n) ((range N).erase 0) := by
  intro m hm n hn he
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (mem_erase.mp hm).1)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (mem_erase.mp hn).1)
  have h := Real.log_injOn_pos hm0 hn0 (neg_injective he)
  exact_mod_cast h

theorem Q_mean_diagonal_offDiagonal (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in -u..u, ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      2 * u * ∑ n ∈ (range ⌈y⌉₊).erase 0, (ArithmeticFunction.moebius n : ℝ) ^ 2 / n +
      2 * ∑ m ∈ (range ⌈y⌉₊).erase 0, ∑ n ∈ ((range ⌈y⌉₊).erase 0).erase m,
        ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ /
          |Real.log m - Real.log n| := by
  have h := finite_mean_le ((range ⌈y⌉₊).erase 0) criticalCoefficient
    (fun n => -Real.log n) (negative_log_inj ⌈y⌉₊) hu
  have hd : (∑ n ∈ (range ⌈y⌉₊).erase 0, ‖criticalCoefficient n‖ ^ 2) =
      ∑ n ∈ (range ⌈y⌉₊).erase 0, (ArithmeticFunction.moebius n : ℝ) ^ 2 / n := by
    apply sum_congr rfl
    intro n hn
    exact criticalCoefficient_sq (Nat.pos_of_ne_zero (mem_erase.mp hn).1)
  have he (m n : ℕ) : |-Real.log m - -Real.log n| = |Real.log m - Real.log n| := by
    rw [show -Real.log m - -Real.log n = -(Real.log m - Real.log n) by ring, abs_neg]
  simp_rw [Q_eq_exponential, he] at *
  rwa [hd] at h

theorem Q_mean_integrable (y u : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2)
      volume (-u) u := by
  simp_rw [Q_eq_exponential]
  apply Continuous.intervalIntegrable
  unfold exponentialPolynomial wave
  fun_prop

end LiuWang.Proof.GlobalZeroDensity.Sharp
