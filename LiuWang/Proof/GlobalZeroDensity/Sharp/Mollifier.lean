import LiuWang.Proof.GlobalZeroDensity.CriticalLine

/-! Keeping the whole family of multiples of four in the strict-cutoff mollifier. -/

set_option autoImplicit false

noncomputable section

open Finset Complex

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem moebius_eq_zero_of_four_dvd {n : ℕ} (hn : 4 ∣ n) :
    ArithmeticFunction.moebius n = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) (by simpa using hn)

theorem sqrt_difference_le_inv {x : ℝ} (hx : 1 ≤ x) :
    2 * (Real.sqrt (x + 1) - Real.sqrt x) ≤ (Real.sqrt x)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have ha := Real.sq_sqrt hx0.le
  have hb := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hab := Real.sqrt_le_sqrt (show x ≤ x + 1 by linarith)
  have hp := Real.sqrt_pos.mpr hx0
  rw [← one_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith [sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x)]

theorem sum_inv_sqrt_lower (N : ℕ) :
    2 * Real.sqrt N - 2 ≤ ∑ n ∈ range N, (Real.sqrt (n : ℝ))⁻¹ := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ]
    by_cases hN : N = 0
    · subst N; norm_num
    have h := sqrt_difference_le_inv
      (show (1 : ℝ) ≤ N by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)
    simp only [Nat.cast_add, Nat.cast_one] at *
    linarith

theorem sqrt_floor_quarter_lower (N : ℕ) :
    Real.sqrt N / 2 - 1 ≤ Real.sqrt (N / 4 : ℕ) := by
  have hdiv : (N : ℝ) ≤ 4 * (N / 4 : ℕ) + 3 := by
    exact_mod_cast (show N ≤ 4 * (N / 4) + 3 by omega)
  have hN := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hK := Real.sq_sqrt (Nat.cast_nonneg (N / 4) : (0 : ℝ) ≤ (N / 4 : ℕ))
  nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sqrt_nonneg ((N / 4 : ℕ) : ℝ)]

theorem sum_four_multiples (N : ℕ) :
    (∑ n ∈ (range (N / 4)).image (fun k : ℕ => 4 * k), (Real.sqrt (n : ℝ))⁻¹) =
      (1 / 2) * ∑ k ∈ range (N / 4), (Real.sqrt (k : ℝ))⁻¹ := by
  rw [sum_image (fun a _ b _ h => by omega), mul_sum]
  apply sum_congr rfl
  intro n _
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num [mul_inv_rev, mul_comm]

theorem norm_Q_le_sub_four (y t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
      (∑ n ∈ range ⌈y⌉₊, (Real.sqrt (n : ℝ))⁻¹) -
      (1 / 2) * ∑ k ∈ range (⌈y⌉₊ / 4), (Real.sqrt (k : ℝ))⁻¹ := by
  let A := (range (⌈y⌉₊ / 4)).image (fun k => 4 * k)
  have hsub : A ⊆ range ⌈y⌉₊ := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    rw [mem_range] at hk ⊢
    omega
  have hnorm :
      ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
        ∑ n ∈ range ⌈y⌉₊ \ A, (Real.sqrt (n : ℝ))⁻¹ := by
    have hQ : Q y ((1 / 2 : ℂ) + t * Complex.I) =
        ∑ n ∈ range ⌈y⌉₊ \ A, (ArithmeticFunction.moebius n : ℂ) /
          (n : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I) := by
      unfold Q
      rw [← sum_sdiff hsub]
      have hz : (∑ n ∈ A, (ArithmeticFunction.moebius n : ℂ) /
          (n : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I)) = 0 := by
        apply sum_eq_zero
        intro n hn
        obtain ⟨k, _, rfl⟩ := mem_image.mp hn
        simp [moebius_eq_zero_of_four_dvd (show 4 ∣ 4 * k from dvd_mul_right 4 k)]
      rw [hz, add_zero]
    rw [hQ]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n _
    by_cases hn : n = 0
    · subst n; simp
    have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hre : (((1 / 2 : ℂ) + t * Complex.I).re) = 1 / 2 := by simp
    rw [hre, ← Real.sqrt_eq_rpow, ← one_div]
    exact div_le_div_of_nonneg_right hmu (Real.sqrt_nonneg _)
  have heq := sum_sdiff hsub (f := fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
  change (∑ n ∈ range ⌈y⌉₊ \ A, _) + (∑ n ∈
    (range (⌈y⌉₊ / 4)).image (fun k : ℕ => 4 * k), _) = _ at heq
  rw [sum_four_multiples] at heq
  linarith

theorem norm_Q_three_halves (y t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
      (3 / 2) * Real.sqrt ⌈y⌉₊ + 2 := by
  have h := norm_Q_le_sub_four y t
  have hu := sum_inv_sqrt_le ⌈y⌉₊
  have hl := sum_inv_sqrt_lower (⌈y⌉₊ / 4)
  have hk := sqrt_floor_quarter_lower ⌈y⌉₊
  linarith

theorem norm_Q_eight_fifths {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ (8 / 5) * Real.sqrt y := by
  have hy0 : 0 ≤ y := by linarith
  have hceil : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hsq := Real.sq_sqrt hy0
  have hsqc := Real.sq_sqrt (Nat.cast_nonneg ⌈y⌉₊ : (0 : ℝ) ≤ ⌈y⌉₊)
  have hs : 100 ≤ Real.sqrt y := by
    have h := Real.sqrt_le_sqrt hy
    norm_num at h
    exact h
  have hc : Real.sqrt ⌈y⌉₊ ≤ Real.sqrt y + 1 := by
    nlinarith [Real.sqrt_nonneg (⌈y⌉₊ : ℝ)]
  exact (norm_Q_three_halves y t).trans (by linarith)

theorem norm_Q_sq_le {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ (64 / 25) * y := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_Q_eight_fifths hy t) 2
  have hs := Real.sq_sqrt (show 0 ≤ y by linarith)
  nlinarith

theorem mollifier_source_bound {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (2583 / 1000) * y + (608 / 1000) * Real.log y + 5608 / 1000 := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have h := norm_Q_sq_le hy t
  linarith

end LiuWang.Proof.GlobalZeroDensity.Sharp
