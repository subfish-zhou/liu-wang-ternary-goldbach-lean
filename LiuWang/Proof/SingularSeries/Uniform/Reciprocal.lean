import LiuWang.Proof.SingularSeries.Uniform.FiniteSums

/-! Elementary reciprocal-square tails by exact telescoping, without numerical search. -/

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SingularSeries.Uniform

theorem reciprocal_square_step {n : ℕ} (hn : 0 < n) :
    1 / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  push_cast
  field_simp
  nlinarith

theorem reciprocal_square_tail {m B : ℕ} (hm : 0 < m) (hB : m ≤ B) :
    (∑ n ∈ Icc (m + 1) B, 1 / (n : ℝ) ^ 2) ≤ 1 / (m : ℝ) - 1 / (B : ℝ) := by
  induction B, hB using Nat.le_induction with
  | base => simp
  | succ B hB ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h := reciprocal_square_step (hm.trans_le hB)
    linarith

theorem reciprocal_square_tail_le {m B : ℕ} (hm : 0 < m) :
    (∑ n ∈ Icc (m + 1) B, 1 / (n : ℝ) ^ 2) ≤ 1 / (m : ℝ) := by
  by_cases hB : m ≤ B
  · exact (reciprocal_square_tail hm hB).trans (sub_le_self _ (by positivity))
  · rw [Icc_eq_empty_of_lt (by omega), sum_empty]
    positivity

theorem reciprocal_square_prefix (X : ℕ) :
    (∑ n ∈ Icc 1 X, 1 / (n : ℝ) ^ 2) ≤ (5 / 3 : ℝ) := by
  by_cases hX : X ≤ 5
  · calc
      _ ≤ ∑ n ∈ Icc 1 (5 : ℕ), 1 / (n : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hX) (by intros; positivity)
      _ ≤ _ := by norm_num [sum_Icc_succ_top]
  · have he : (∑ n ∈ Icc 1 X, 1 / (n : ℝ) ^ 2) =
        (∑ n ∈ Icc 1 (5 : ℕ), 1 / (n : ℝ) ^ 2) +
        ∑ n ∈ Icc 6 X, 1 / (n : ℝ) ^ 2 := by
      have h := sum_Ico_consecutive (fun n : ℕ => 1 / (n : ℝ) ^ 2)
        (show 1 ≤ 6 by norm_num) (show 6 ≤ X + 1 by omega)
      have he (a b : ℕ) : Ico a (b + 1) = Icc a b := by ext n; simp
      simpa only [he] using h.symm
    rw [he]
    have h := reciprocal_square_tail_le (m := 5) (B := X) (by norm_num)
    norm_num [sum_Icc_succ_top] at h ⊢
    linarith

theorem reciprocal_square_sixth_constant : (5 / 3 : ℝ) ^ 6 < 22 := by norm_num

end LiuWang.Proof.SingularSeries.Uniform
