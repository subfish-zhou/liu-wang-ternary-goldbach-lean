import LiuWang.Proof.Campaign20260915.Density.ResidueTail

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.Campaign20260915.Density

theorem nearGap_residue_row {q : ℕ} [NeZero q] (S : Finset ℕ) (x : ZMod q)
    {m : ℕ} (hm : m ∈ fiber q S x) (hm0 : 0 < m) :
    (∑ n ∈ fiber q S x, nearGap m n) ≤ (2 / q) * (3 + Real.log m) := by
  let T := S.filter (fun n => n ≤ 2 * m ∧ m ≤ 2 * n)
  have hT : T ⊆ range (2 * m + 1) := by
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hn).2.1)
  have hmT : m ∈ fiber q T x := by
    obtain ⟨hmS, hmx⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hmS, by omega⟩, hmx⟩
  have he : (∑ n ∈ fiber q S x, nearGap m n) =
      ∑ n ∈ fiber q T x, 1 / |(m : ℝ) - n| := by
    simp only [nearGap, ← sum_filter]
    congr 1
    ext n
    simp [fiber, T, and_left_comm, and_assoc, and_comm]
  rw [he]
  have h := congruence_gap_row hT x hmT
  let K : ℕ := (2 * m + 1) / q + 1
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.mpr (Nat.succ_pos ((2 * m + 1) / q))
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hK : (K : ℝ) ≤ 4 * m := by
    have hdiv := Nat.div_le_self (2 * m + 1) q
    exact_mod_cast (show K ≤ 4 * m by dsimp [K]; omega)
  have hlog := Real.log_le_log hK0 hK
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hmR.ne'] at hlog
  have hfour : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hH := inverse_range_le_log K
  have hbudget : harmonicRange K ≤ 3 + Real.log m := by
    unfold harmonicRange
    linarith
  exact h.trans (mul_le_mul_of_nonneg_left hbudget (by positivity))

theorem residue_weighted_off_diagonal {q : ℕ} [NeZero q] (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (x : ZMod q) (A : ℕ → ℝ) (hA : ∀ n ∈ S, 0 ≤ A n) :
    (∑ m ∈ fiber q S x, ∑ n ∈ fiber q S x,
      A m * A n / |Real.log m - Real.log n|) ≤
      (2 / q) * (∑ n ∈ fiber q S x, (n : ℝ) * A n ^ 2 * (3 + Real.log n)) +
        2 * (∑ n ∈ fiber q S x, A n) ^ 2 := by
  have h := weighted_off_diagonal_rows (fiber q S x)
    (fun n hn => hS n (mem_filter.mp hn).1) A
    (fun n hn => hA n (mem_filter.mp hn).1)
    (fun n => (2 / q) * (3 + Real.log n))
    (fun n hn => nearGap_residue_row S x hn (hS n (mem_filter.mp hn).1))
  convert h using 1
  rw [mul_sum]
  congr 1
  exact sum_congr rfl (fun _ _ => by ring)

theorem rightTerm_reweighted {X d : ℝ} (hX : 1 < X) {n : ℕ} (hn : 0 < n) :
    ‖rightTerm X (1 + d) n‖ ^ 2 * (n : ℝ) ^ (1 + d) ≤
      (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + d)) := by
  rw [rightTerm_square X d hn, mul_assoc, ← Real.rpow_add (Nat.cast_pos.mpr hn),
    show -(2 + 2 * d) + (1 + d) = -(1 + d) by ring]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (GlobalZeroDensity.coefficient_norm_le hX n) 2)
    (by positivity)

theorem residue_rightTerm_mass {q : ℕ} [NeZero q] {S : Finset ℕ} (x : ZMod q)
    {X d : ℝ} (hX : 2 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1)
    (hS : ∀ n ∈ S, X ≤ (n : ℝ)) :
    (∑ n ∈ fiber q S x, ‖rightTerm X (1 + d) n‖) ^ 2 ≤
      ((2 / q) * X ^ (-d) * (1 + 1 / d)) *
        ∑ n ∈ fiber q S x, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + d)) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX1 : 1 < X := by linarith
  have hp (n : ℕ) (hn : n ∈ fiber q S x) : 0 < n := by
    have : (0 : ℝ) < n := by linarith [hS n (mem_filter.mp hn).1]
    exact_mod_cast this
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (fiber q S x)
    (r := fun n => ‖rightTerm X (1 + d) n‖)
    (f := fun n => ‖rightTerm X (1 + d) n‖ ^ 2 * (n : ℝ) ^ (1 + d))
    (g := fun n => (n : ℝ) ^ (-(1 + d)))
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun n hn => le_of_eq (by
      rw [mul_assoc, ← Real.rpow_add (Nat.cast_pos.mpr (hp n hn))]
      simp))
  have hE := sum_le_sum (fun n hn => rightTerm_reweighted (d := d) hX1 (hp n hn))
  have htail := residue_power_tail x hX hd hd1 hS
  have hmul := mul_le_mul hE htail (sum_nonneg (fun _ _ => by positivity))
    (sum_nonneg (fun _ _ => by positivity))
  exact hcs.trans (hmul.trans_eq (mul_comm _ _))

theorem sum_all_fibers (q : ℕ) [NeZero q] (S : Finset ℕ) (W : ℕ → ℝ) :
    (∑ x : ZMod q, ∑ n ∈ fiber q S x, W n) = ∑ n ∈ S, W n := by
  simp only [fiber, sum_filter]
  rw [sum_comm]
  simp

#print axioms residue_weighted_off_diagonal
#print axioms residue_rightTerm_mass

end LiuWang.Proof.Campaign20260915.Density
