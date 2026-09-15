import LiuWang.Proof.Campaign20260915.Density.DivisorMoments

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

namespace LiuWang.Proof.Campaign20260915.Density

theorem reciprocal_square_finite {S : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N ≤ n) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ 2) ≤ 2 / (N : ℝ) := by
  have he : (∑ n ∈ S, 1 / (n : ℝ) ^ 2) =
      ∑ k ∈ S.image (fun n => n - N), 1 / ((k + N : ℕ) : ℝ) ^ 2 := by
    rw [sum_image (fun a ha b hb hab => by
      have := hS a ha
      have := hS b hb
      omega)]
    exact sum_congr rfl (fun n hn => by rw [Nat.sub_add_cancel (hS n hn)])
  rw [he]
  have hs := (summable_nat_add_iff N).mpr hasSum_zeta_two.summable
  have h := (hs.sum_le_tsum (S.image (fun n => n - N)) (fun _ _ => by positivity)).trans
    (reciprocal_sq_tail hN)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : 1 / (N : ℝ) ^ 2 ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc
    _ ≤ 1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) := h
    _ ≤ 1 / (N : ℝ) + 1 / (N : ℝ) := add_le_add hi le_rfl
    _ = 2 / (N : ℝ) := by ring

theorem reciprocal_square_real_tail {S : Finset ℕ} {c : ℝ} (hc : 1 ≤ c)
    (hS : ∀ n ∈ S, c ≤ (n : ℝ)) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ 2) ≤ 2 / c := by
  have hceil := Nat.le_ceil c
  have hN : 0 < ⌈c⌉₊ := by
    have : (1 : ℝ) ≤ ⌈c⌉₊ := hc.trans hceil
    exact_mod_cast this
  exact (reciprocal_square_finite hN (fun n hn => Nat.ceil_le.mpr (hS n hn))).trans
    (div_le_div_of_nonneg_left (by norm_num) (by linarith) hceil)

def cutoffReciprocal (X : ℕ) (y : ℝ) (g : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, if y ≤ (g * a : ℕ) then 1 / (a : ℝ) ^ 2 else 0

theorem cutoffReciprocal_nonneg (X : ℕ) (y : ℝ) (g : ℕ) :
    0 ≤ cutoffReciprocal X y g := by
  exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem cutoffReciprocal_le_two (X : ℕ) (y : ℝ) (g : ℕ) :
    cutoffReciprocal X y g ≤ 2 := by
  have h := reciprocal_square_finite (S := Icc 1 X) (by omega : 0 < 1)
    (fun _ hn => (mem_Icc.mp hn).1)
  have hpoint (a : ℕ) (_ha : a ∈ Icc 1 X) :
      (if y ≤ (g * a : ℕ) then 1 / (a : ℝ) ^ 2 else 0) ≤ 1 / (a : ℝ) ^ 2 := by
    split_ifs
    · exact le_rfl
    · positivity
  exact (sum_le_sum hpoint).trans (by simpa using h)

theorem cutoffReciprocal_le_scaled (X : ℕ) {y : ℝ} {g : ℕ}
    (hg : 0 < g) (hgy : (g : ℝ) ≤ y) :
    cutoffReciprocal X y g ≤ 2 * g / y := by
  have hgr : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hc : 1 ≤ y / g := (le_div_iff₀ hgr).mpr (by simpa using hgy)
  have h := reciprocal_square_real_tail
    (S := (Icc 1 X).filter (fun a => y ≤ (g * a : ℕ))) hc (fun n hn => by
      have hn' := (mem_filter.mp hn).2
      rw [div_le_iff₀ hgr]
      simpa [Nat.cast_mul, mul_comm] using hn')
  rw [sum_filter] at h
  exact h.trans_eq (by field_simp)

theorem large_divisor_square_reciprocal (X : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ Icc 1 X, ((largeDivisors y n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
      24 / y := by
  have h := large_divisor_square_weight_le X y (fun n => 1 / (n : ℝ) ^ 2)
    (fun _ => by positivity)
  simp only [mul_one_div] at h
  have he (g a b k : ℕ) :
      (if y ≤ (g * a : ℕ) ∧ y ≤ (g * b : ℕ)
        then 1 / ((g * a * b * k : ℕ) : ℝ) ^ 2 else 0) =
      (1 / (g : ℝ) ^ 2) *
        (if y ≤ (g * a : ℕ) then 1 / (a : ℝ) ^ 2 else 0) *
        (if y ≤ (g * b : ℕ) then 1 / (b : ℝ) ^ 2 else 0) *
        (1 / (k : ℝ) ^ 2) := by
    by_cases ha : y ≤ (g * a : ℕ) <;> by_cases hb : y ≤ (g * b : ℕ) <;>
      simp only [ha, hb, and_self, and_false, false_and, ite_true, ite_false,
        mul_zero, zero_mul]
    simp only [Nat.cast_mul, mul_pow, one_div, mul_inv_rev]
    ring
  simp_rw [he] at h
  have heq :
      (∑ g ∈ Icc 1 X, ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ k ∈ Icc 1 X,
        (1 / (g : ℝ) ^ 2) *
          (if y ≤ (g * a : ℕ) then 1 / (a : ℝ) ^ 2 else 0) *
          (if y ≤ (g * b : ℕ) then 1 / (b : ℝ) ^ 2 else 0) *
          (1 / (k : ℝ) ^ 2)) =
      (∑ g ∈ Icc 1 X, cutoffReciprocal X y g ^ 2 / (g : ℝ) ^ 2) *
        (∑ k ∈ Icc 1 X, 1 / (k : ℝ) ^ 2) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro g _
    simp only [← mul_sum, ← sum_mul, cutoffReciprocal]
    ring
  rw [heq] at h
  have hpoint (g : ℕ) (hg : g ∈ Icc 1 X) :
      cutoffReciprocal X y g ^ 2 / (g : ℝ) ^ 2 ≤
        if (g : ℝ) ≤ y then 4 / y ^ 2 else 4 / (g : ℝ) ^ 2 := by
    have hg0 : 0 < g := (mem_Icc.mp hg).1
    by_cases hgy : (g : ℝ) ≤ y
    · rw [if_pos hgy]
      have hh := pow_le_pow_left₀ (cutoffReciprocal_nonneg X y g)
        (cutoffReciprocal_le_scaled X hg0 hgy) 2
      apply (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq
      field_simp
      ring
    · rw [if_neg hgy]
      exact div_le_div_of_nonneg_right
        (by nlinarith [cutoffReciprocal_le_two X y g,
          cutoffReciprocal_nonneg X y g]) (sq_nonneg _)
  let A := (Icc 1 X).filter (fun g : ℕ => (g : ℝ) ≤ y)
  let B := (Icc 1 X).filter (fun g : ℕ => ¬(g : ℝ) ≤ y)
  have hA : (A.card : ℝ) ≤ y := by
    have hsub : A ⊆ Icc 1 ⌊y⌋₊ := by
      intro g hg
      obtain ⟨hg, hgy⟩ := mem_filter.mp hg
      exact mem_Icc.mpr ⟨(mem_Icc.mp hg).1, Nat.le_floor hgy⟩
    have hh : (A.card : ℝ) ≤ ⌊y⌋₊ := by
      exact_mod_cast (show A.card ≤ ⌊y⌋₊ by simpa using card_le_card hsub)
    exact hh.trans (Nat.floor_le (by linarith))
  have hB := reciprocal_square_real_tail (S := B) hy
    (fun g hg => (lt_of_not_ge (mem_filter.mp hg).2).le)
  have hsplit : (∑ g ∈ Icc 1 X,
      if (g : ℝ) ≤ y then 4 / y ^ 2 else 4 / (g : ℝ) ^ 2) =
      (A.card : ℝ) * (4 / y ^ 2) + 4 * ∑ g ∈ B, 1 / (g : ℝ) ^ 2 := by
    have hconst : (A.card : ℝ) * (4 / y ^ 2) = ∑ _g ∈ A, 4 / y ^ 2 := by simp
    rw [hconst, mul_sum]
    simp only [A, B, sum_filter, ← sum_add_distrib, mul_one_div]
    apply sum_congr rfl
    intro g _
    split_ifs <;> simp
  have hlow : (A.card : ℝ) * (4 / y ^ 2) ≤ 4 / y := by
    apply (mul_le_mul_of_nonneg_right hA (by positivity)).trans_eq
    field_simp
  have henergy : (∑ g ∈ Icc 1 X, cutoffReciprocal X y g ^ 2 / (g : ℝ) ^ 2) ≤
      12 / y := by
    have hh := sum_le_sum hpoint
    rw [hsplit] at hh
    calc
      _ ≤ (A.card : ℝ) * (4 / y ^ 2) + 4 * ∑ g ∈ B, 1 / (g : ℝ) ^ 2 := hh
      _ ≤ 4 / y + 4 * (2 / y) :=
        add_le_add hlow (mul_le_mul_of_nonneg_left hB (by norm_num))
      _ = 12 / y := by ring
  have htwo := reciprocal_square_finite (S := Icc 1 X) (by omega : 0 < 1)
    (fun _ hn => (mem_Icc.mp hn).1)
  norm_num at htwo
  have hprod := mul_le_mul henergy htwo (sum_nonneg (fun _ _ => by positivity))
    (by positivity : 0 ≤ 12 / y)
  calc
    _ ≤ (∑ g ∈ Icc 1 X, cutoffReciprocal X y g ^ 2 / (g : ℝ) ^ 2) *
        (∑ k ∈ Icc 1 X, 1 / (k : ℝ) ^ 2) := h
    _ ≤ (12 / y) * 2 := by simpa only [one_div] using hprod
    _ = 24 / y := by ring

#print axioms large_divisor_square_reciprocal

theorem detector_reciprocal_energy {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ S, ‖GlobalZeroDensity.coefficient y n‖ ^ 2 / (n : ℝ) ^ 2) ≤ 24 / y := by
  have hsub : S ⊆ Icc 1 (S.sup id) := fun n hn =>
    mem_Icc.mpr ⟨hS n hn, le_sup (f := id) hn⟩
  calc
    _ ≤ ∑ n ∈ S, ((largeDivisors y n).card : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
      sum_le_sum (fun n _ => div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (coefficient_norm_le_large_divisors y n) 2)
        (sq_nonneg _))
    _ ≤ ∑ n ∈ Icc 1 (S.sup id),
        ((largeDivisors y n).card : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 24 / y := large_divisor_square_reciprocal _ hy

theorem detector_right_diagonal {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {y d : ℝ} (hy : 1 ≤ y) (hd : 0 ≤ d) :
    (∑ n ∈ S, ‖GlobalZeroDensity.coefficient y n‖ ^ 2 *
      (n : ℝ) ^ (-(2 + 2 * d))) ≤ (24 / y) * y ^ (-2 * d) := by
  have hpoint (n : ℕ) (hn : n ∈ S) :
      ‖GlobalZeroDensity.coefficient y n‖ ^ 2 * (n : ℝ) ^ (-(2 + 2 * d)) ≤
        (‖GlobalZeroDensity.coefficient y n‖ ^ 2 / (n : ℝ) ^ 2) * y ^ (-2 * d) := by
    by_cases hny : (n : ℝ) < y
    · simp [GlobalZeroDensity.coefficient_eq_zero_of_lt hny]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hS n hn)
    have hr := Real.rpow_le_rpow_of_nonpos (show 0 < y by linarith)
      (le_of_not_gt hny) (show -2 * d ≤ 0 by linarith)
    rw [show -(2 + 2 * d) = -2 + (-2 * d) by ring, Real.rpow_add hn0]
    rw [Real.rpow_neg hn0.le, Real.rpow_two]
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_of_nonneg_left hr
        (show 0 ≤ ‖GlobalZeroDensity.coefficient y n‖ ^ 2 / (n : ℝ) ^ 2 by positivity)
  have h := sum_le_sum hpoint
  rw [← sum_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right (detector_reciprocal_energy hS hy)
    (Real.rpow_nonneg (by linarith) _))

theorem twisted_detector_right_diagonal {q : ℕ} (chi : Interfaces.Character q)
    {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) {y d : ℝ} (hy : 1 ≤ y) (hd : 0 ≤ d) :
    (∑ n ∈ S, ‖NonprincipalDensityAdvance.coefficient chi y n‖ ^ 2 *
      (n : ℝ) ^ (-(2 + 2 * d))) ≤ (24 / y) * y ^ (-2 * d) := by
  apply le_trans (sum_le_sum (fun n _ => ?_)) (detector_right_diagonal hS hy hd)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [NonprincipalDensityAdvance.coefficient, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (chi.norm_le_one n)

#print axioms detector_right_diagonal
#print axioms twisted_detector_right_diagonal

end LiuWang.Proof.Campaign20260915.Density
