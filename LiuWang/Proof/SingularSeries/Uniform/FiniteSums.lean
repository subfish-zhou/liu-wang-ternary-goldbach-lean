import LiuWang.Proof.SingularSeries.Consumer

/-! Finite divisor reindexing and nonnegative Dirichlet-convolution bounds. -/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace LiuWang.Proof.SingularSeries.Uniform

theorem sum_multiples (f : ℕ → ℝ) (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Icc 1 X, if d ∣ q then f q else 0) =
      ∑ k ∈ Icc 1 (X / d), f (d * k) := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun k _ => d * k)
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1, hkX⟩
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkX
  · intro a _ b _ hab
    exact Nat.mul_left_cancel hd hab
  · intro q hq
    rcases mem_filter.mp hq with ⟨hq, ⟨k, rfl⟩⟩
    refine ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have := (mem_Icc.mp hq).1
      by_contra h
      have : k = 0 := by omega
      simp_all
    · exact (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using (mem_Icc.mp hq).2)
  · intros
    rfl

theorem sum_divisors_reindex (X : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 X, ∑ d ∈ q.divisors, F q d) =
      ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X / d), F (d * k) d := by
  have he (q : ℕ) (hq : q ∈ Icc 1 X) :
      (∑ d ∈ q.divisors, F q d) = ∑ d ∈ Icc 1 X, if d ∣ q then F q d else 0 := by
    rw [← sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hq0, (Nat.le_of_dvd hq0 hd).trans (mem_Icc.mp hq).2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, hq0.ne'⟩
  rw [sum_congr rfl he, sum_comm]
  apply sum_congr rfl
  intro d hd
  exact sum_multiples (fun q => F q d) X (mem_Icc.mp hd).1

def squareSum (f : ArithmeticFunction ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, f n / (n : ℝ) ^ 2

theorem squareSum_nonneg {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (X : ℕ) :
    0 ≤ squareSum f X := sum_nonneg fun n _ => div_nonneg (hf n) (sq_nonneg _)

theorem convolution_nonneg {f g : ArithmeticFunction ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f * g) n := by
  rw [mul_apply]
  exact sum_nonneg fun d _ => mul_nonneg (hf d.1) (hg d.2)

theorem squareSum_convolution_le {f g : ArithmeticFunction ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (X : ℕ) :
    squareSum (f * g) X ≤ squareSum f X * squareSum g X := by
  have he (q : ℕ) :
      (f * g) q / (q : ℝ) ^ 2 = ∑ d ∈ q.divisors, f d * g (q / d) / (q : ℝ) ^ 2 := by
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d e => f d * g e), sum_div]
  simp only [squareSum, he]
  rw [sum_divisors_reindex]
  calc
    _ = ∑ d ∈ Icc 1 X, (f d / (d : ℝ) ^ 2) *
        ∑ k ∈ Icc 1 (X / d), g k / (k : ℝ) ^ 2 := by
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      rw [Nat.mul_div_cancel_left _ (mem_Icc.mp hd).1, Nat.cast_mul, mul_pow]
      ring
    _ ≤ ∑ d ∈ Icc 1 X, (f d / (d : ℝ) ^ 2) *
        ∑ k ∈ Icc 1 X, g k / (k : ℝ) ^ 2 := by
      apply sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (hf d) (sq_nonneg _))
      apply sum_le_sum_of_subset_of_nonneg
      · exact Icc_subset_Icc le_rfl (Nat.div_le_self X d)
      · intro k _ _
        exact div_nonneg (hg k) (sq_nonneg _)
    _ = _ := (sum_mul ..).symm

theorem sum_divisor_quotient_le {a : ℕ → ℝ} (ha : ∀ d, 0 ≤ a d) (X : ℕ) :
    (∑ q ∈ Icc 1 X, ∑ d ∈ q.divisors, a d / (d : ℝ)) ≤
      (X : ℝ) * ∑ d ∈ Icc 1 X, a d / (d : ℝ) ^ 2 := by
  rw [sum_divisors_reindex]
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [mul_sum]
  apply sum_le_sum
  intro d _
  calc
    _ ≤ ((X : ℝ) / (d : ℝ)) * (a d / (d : ℝ)) :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le (div_nonneg (ha d) (Nat.cast_nonneg d))
    _ = _ := by ring

end LiuWang.Proof.SingularSeries.Uniform
