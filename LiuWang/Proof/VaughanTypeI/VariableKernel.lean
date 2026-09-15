import LiuWang.Proof.VaughanTypeI.RationalCounting

/-!
# 变截断有理逼近核的独立界

首个半块用既约有理数的非共振距离；之后按 q 长块求和。
常数与原 Lemma 6.4 不同，最高阶 X 项的系数仍为一。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Finset AnalyticNumberTheory.LargeSieve

theorem rational_dist_lower {a q n : ℕ} (hq : 0 < q)
    (hcop : Nat.Coprime a q) (hn : 0 < n) (hnq : n < q) :
    1 / (q : ℝ) ≤ distToInt ((a : ℝ) * n / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hmod : (a * n) % q ≠ 0 := by
    intro hz
    have hdn := hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hz)
    exact (not_le.mpr hnq) (Nat.le_of_dvd hn hdn)
  have hmin : 1 ≤ min ((a * n) % q) (q - (a * n) % q) := by
    have hr := Nat.mod_lt (a * n) hq
    omega
  rw [distToInt_eq_abs_round, ← Nat.cast_mul, abs_sub_round_div_natCast_eq]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmin) hq0.le

theorem small_index_dist_lower {a q n : ℕ} {α θ : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hn : 0 < n) (hnq : 2 * n ≤ q)
    (hθ : |θ| ≤ 1) (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    1 / (2 * (q : ℝ)) ≤ distToInt (α * n) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hnqR : 2 * (n : ℝ) ≤ q := by exact_mod_cast hnq
  have hbase := rational_dist_lower hq hcop hn (by omega)
  have herr : |(a : ℝ) * n / q - α * n| ≤ 1 / (2 * (q : ℝ)) := by
    have heq : (a : ℝ) * n / q - α * n = -(θ * n / (q : ℝ) ^ 2) := by
      rw [hα]
      ring
    rw [heq, abs_neg, abs_div, abs_mul]
    simp only [Nat.abs_cast, abs_pow]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg n)) (sq_nonneg _)).trans
    rw [one_mul]
    apply (div_le_div_iff₀ (sq_pos_of_pos hqp) (by positivity)).mpr
    nlinarith
  have htri : distToInt ((a : ℝ) * n / q) ≤
      |(a : ℝ) * n / q - α * n| + distToInt (α * n) := by
    calc
      _ ≤ |(a : ℝ) * n / q - (round (α * n) : ℤ)| := distToInt_le_sub _ _
      _ ≤ |(a : ℝ) * n / q - α * n| + |α * n - (round (α * n) : ℤ)| :=
        abs_sub_le _ _ _
      _ = _ := by rw [← distToInt_eq_abs_round]
  have hhalf : 1 / (q : ℝ) = 2 * (1 / (2 * (q : ℝ))) := by ring
  linarith

private theorem sum_blocks (F : ℕ → ℝ) (H q J : ℕ) :
    (∑ j ∈ range J, ∑ k ∈ range q, F (H + j * q + k)) =
      ∑ n ∈ Ico H (H + J * q), F n := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, ih]
      have hshift : (∑ k ∈ range q, F (H + J * q + k)) =
          ∑ n ∈ Ico (H + J * q) (H + (J + 1) * q), F n := by
        rw [sum_Ico_eq_sum_range]
        have he : H + (J + 1) * q - (H + J * q) = q := by
          simp only [add_mul, one_mul]
          omega
        rw [he]
      rw [hshift, sum_Ico_consecutive F (by omega) (by
        simp only [add_mul, one_mul]
        omega)]

private theorem first_half_kernel_le {a q : ℕ} {α θ Y : ℝ}
    (hq : 2 ≤ q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    (∑ n ∈ Ico 1 (q / 2 + 1), truncatedKernel (Y / n) (α * n)) ≤
      3 * (q : ℝ) + (q : ℝ) * (1 + Real.log q) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  calc
    _ ≤ ∑ n ∈ Ico 1 (q / 2 + 1), truncatedKernel (q : ℝ) (α * n) := by
      apply sum_le_sum
      intro n hn
      have hnp := (mem_Ico.mp hn).1
      have hnq : 2 * n ≤ q := by have := (mem_Ico.mp hn).2; omega
      have hd := small_index_dist_lower (by omega) hcop hnp hnq hθ hα
      have hdp : 0 < distToInt (α * n) := (by positivity : 0 < 1 / (2 * (q : ℝ))).trans_le hd
      have hinv : 1 / (2 * distToInt (α * n)) ≤ (q : ℝ) := by
        apply (div_le_iff₀ (by positivity)).mpr
        have hd' := (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))).mp hd
        nlinarith
      simp only [truncatedKernel, if_neg hdp.ne', min_eq_right hinv]
      exact min_le_right _ _
    _ = ∑ k ∈ range (q / 2), truncatedKernel (q : ℝ) (α * (1 + k : ℕ)) := by
      rw [sum_Ico_eq_sum_range]
      simp
    _ ≤ ∑ k ∈ range q, truncatedKernel (q : ℝ) (α * (1 + k : ℕ)) :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.div_le_self _ _))
        (fun _ _ _ => truncatedKernel_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := rational_block_kernel_le (by omega) hcop hθ hα (Nat.cast_nonneg _)

theorem variable_kernel_le {a q X : ℕ} {α θ Y : ℝ}
    (hq : 2 ≤ q) (hX : 1 ≤ X) (hY : 0 ≤ Y)
    (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    (∑ n ∈ Icc 1 X, truncatedKernel (Y / n) (α * n)) ≤
      (X : ℝ) * (1 + Real.log q) + (q : ℝ) * (5 + 2 * Real.log q) +
        6 * Y / q * (1 + Real.log X) := by
  have hqn : 0 < q := by omega
  have hqp : (0 : ℝ) < q := by exact_mod_cast hqn
  let H := q / 2 + 1
  let J := X / q + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hHq : q ≤ 2 * H := by dsimp [H]; omega
  have hJX : J ≤ X := by
    dsimp [J]
    have := Nat.div_lt_self (by omega : 0 < X) hq
    omega
  have hJq : J * q ≤ X + q := by
    simpa only [J, add_mul, one_mul] using Nat.add_le_add_right (Nat.div_mul_le_self X q) q
  have hcover : X < H + J * q := by
    have hlt : X < J * q := (Nat.div_lt_iff_lt_mul hqn).mp (Nat.lt_succ_self (X / q))
    omega
  let F := fun n : ℕ => truncatedKernel (Y / n) (α * n)
  have hF : ∀ n, 0 ≤ F n := fun n => truncatedKernel_nonneg (by positivity) _
  have hrow (j : ℕ) :
      (∑ k ∈ range q, F (H + j * q + k)) ≤
        6 * Y / q / (j + 1 : ℕ) + (q : ℝ) * (1 + Real.log q) := by
    have hjp : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    calc
      _ ≤ ∑ k ∈ range q, truncatedKernel (2 * Y / ((q : ℝ) * (j + 1 : ℕ)))
          (α * (H + j * q + k : ℕ)) := by
        apply sum_le_sum
        intro k _
        apply truncatedKernel_mono
        have hp : (0 : ℝ) < (H + j * q + k : ℕ) := by exact_mod_cast (by omega : 0 < H + j * q + k)
        apply (div_le_div_iff₀ hp (mul_pos hqp hjp)).mpr
        have hl : q * (j + 1) ≤ 2 * (H + j * q + k) := by nlinarith
        have hlR : (q : ℝ) * (j + 1 : ℕ) ≤ 2 * (H + j * q + k : ℕ) := by exact_mod_cast hl
        nlinarith [mul_nonneg hY (sub_nonneg.mpr hlR)]
      _ ≤ 3 * (2 * Y / ((q : ℝ) * (j + 1 : ℕ))) + (q : ℝ) * (1 + Real.log q) :=
        rational_block_kernel_le hqn hcop hθ hα (by positivity)
      _ = _ := by ring
  have htail : (∑ j ∈ range J, ∑ k ∈ range q, F (H + j * q + k)) ≤
      6 * Y / q * (1 + Real.log X) + ((X : ℝ) + q) * (1 + Real.log q) := by
    calc
      _ ≤ ∑ j ∈ range J, (6 * Y / q / (j + 1 : ℕ) + (q : ℝ) * (1 + Real.log q)) :=
        sum_le_sum (fun j _ => hrow j)
      _ = 6 * Y / q * (harmonic J : ℝ) + (J : ℝ) * q * (1 + Real.log q) := by
        simp only [sum_add_distrib, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          Rat.cast_add, Rat.cast_one, div_eq_mul_inv, mul_sum, sum_const, card_range,
          nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ _ := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (harmonic_le_one_add_log J).trans
            (add_le_add_right (Real.log_le_log (by dsimp [J]; positivity)
              (by exact_mod_cast hJX)) _)
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJq)
            (by linarith [Real.log_natCast_nonneg q])
  calc
    _ ≤ ∑ n ∈ Ico 1 (H + J * q), F n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Ico.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans_lt hcover⟩
      · exact fun n _ _ => hF n
    _ = (∑ n ∈ Ico 1 H, F n) + ∑ j ∈ range J, ∑ k ∈ range q, F (H + j * q + k) := by
      rw [sum_blocks, sum_Ico_consecutive F hH (by omega)]
    _ ≤ (3 * (q : ℝ) + (q : ℝ) * (1 + Real.log q)) +
        (6 * Y / q * (1 + Real.log X) + ((X : ℝ) + q) * (1 + Real.log q)) :=
      add_le_add (first_half_kernel_le hq hcop hθ hα) htail
    _ = _ := by ring

end LiuWang.Proof.VaughanTypeI
