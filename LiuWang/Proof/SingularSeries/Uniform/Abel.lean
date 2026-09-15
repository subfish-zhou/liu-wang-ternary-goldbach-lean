import LiuWang.Proof.SingularSeries.Uniform.Mean

/-! Finite Abel summation retains the lower endpoint correctly before taking any infinite sum. -/

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SingularSeries.Uniform

theorem finite_abel (f w : ℕ → ℝ) {m B : ℕ} (hmB : m ≤ B) :
    (∑ q ∈ Icc m B, f q * w q) =
      (∑ q ∈ Icc m B, f q) * w B +
      ∑ k ∈ Ico m B, (∑ q ∈ Icc m k, f q) * (w k - w (k + 1)) := by
  induction B, hmB using Nat.le_induction with
  | base => simp
  | succ B hmB ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega),
      sum_Ico_succ_top hmB, ih]
    ring

theorem weighted_sum_le_of_prefix_le (f g w : ℕ → ℝ) {m B : ℕ} (hmB : m ≤ B)
    (hs : ∀ k, m ≤ k → k ≤ B → (∑ q ∈ Icc m k, f q) ≤ ∑ q ∈ Icc m k, g q)
    (hw : 0 ≤ w B) (hdec : ∀ k, m ≤ k → k < B → w (k + 1) ≤ w k) :
    (∑ q ∈ Icc m B, f q * w q) ≤ ∑ q ∈ Icc m B, g q * w q := by
  rw [finite_abel f w hmB, finite_abel g w hmB]
  apply add_le_add (mul_le_mul_of_nonneg_right (hs B hmB le_rfl) hw)
  apply sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (hs k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2.le)
    (sub_nonneg.mpr (hdec k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2))

def comparisonSequence (m : ℕ) (q : ℕ) : ℝ :=
  if q = m then 22 * (m : ℝ) else 22

theorem comparisonSequence_sum {m B : ℕ} (hmB : m ≤ B) :
    (∑ q ∈ Icc m B, comparisonSequence m q) = 22 * (B : ℝ) := by
  induction B, hmB using Nat.le_induction with
  | base => simp [comparisonSequence]
  | succ B hmB ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    simp only [comparisonSequence, if_neg (show B + 1 ≠ m by omega), Nat.cast_add, Nat.cast_one]
    ring

theorem comparisonSequence_weighted_sum (w : ℕ → ℝ) {m B : ℕ} (hmB : m ≤ B) :
    (∑ q ∈ Icc m B, comparisonSequence m q * w q) =
      22 * (m : ℝ) * w m + 22 * ∑ q ∈ Icc (m + 1) B, w q := by
  induction B, hmB using Nat.le_induction with
  | base => simp [comparisonSequence]
  | succ B hmB ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih]
    simp only [comparisonSequence, if_neg (show B + 1 ≠ m by omega)]
    ring

theorem reciprocal_weight_antitone {k : ℕ} (hk : 0 < k) :
    1 / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) ^ 2 := by
  apply one_div_le_one_div_of_le (by positivity)
  have h : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) h 2

theorem ratioSquare_weighted_tail_finite {m B : ℕ} (hm : 1 ≤ m) :
    (∑ q ∈ Icc m B, ratioSquare q / (q : ℝ) ^ 2) ≤ 44 / (m : ℝ) := by
  by_cases hmB : m ≤ B
  · have hdom := weighted_sum_le_of_prefix_le ratioSquare (comparisonSequence m)
      (fun q => 1 / (q : ℝ) ^ 2) hmB (by
        intro k hmk _
        rw [comparisonSequence_sum hmk]
        exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc hm le_rfl)
          (fun q _ _ => ratioSquare_nonneg q)).trans (ratioSquare_sum_le k))
      (by positivity) (by
        intro k hmk _
        exact reciprocal_weight_antitone (lt_of_lt_of_le (by omega : 0 < m) hmk))
    rw [comparisonSequence_weighted_sum _ hmB] at hdom
    simp only [mul_one_div] at hdom
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have he : 22 * (m : ℝ) / (m : ℝ) ^ 2 = 22 / (m : ℝ) := by field_simp
    rw [he] at hdom
    have ht := reciprocal_square_tail_le (m := m) (B := B) (by omega)
    calc
      _ ≤ 22 / (m : ℝ) + 22 * ∑ q ∈ Icc (m + 1) B, 1 / (q : ℝ) ^ 2 := hdom
      _ ≤ 22 / (m : ℝ) + 22 * (1 / (m : ℝ)) := by gcongr
      _ = _ := by ring
  · rw [Icc_eq_empty_of_lt (by omega), sum_empty]
    positivity

theorem inverse_totient_sq_eq_weighted_ratio {q : ℕ} (hq : 0 < q) :
    1 / (q.totient : ℝ) ^ 2 = ratioSquare q / (q : ℝ) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold ratioSquare
  field_simp

theorem inverse_totient_tail_finite {m B : ℕ} (hm : 1 ≤ m) :
    (∑ q ∈ Icc m B, 1 / (q.totient : ℝ) ^ 2) ≤ 44 / (m : ℝ) := by
  have he : (∑ q ∈ Icc m B, 1 / (q.totient : ℝ) ^ 2) =
      ∑ q ∈ Icc m B, ratioSquare q / (q : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro q hq
    exact inverse_totient_sq_eq_weighted_ratio (by have := (mem_Icc.mp hq).1; omega)
  rw [he]
  exact ratioSquare_weighted_tail_finite hm

end LiuWang.Proof.SingularSeries.Uniform
