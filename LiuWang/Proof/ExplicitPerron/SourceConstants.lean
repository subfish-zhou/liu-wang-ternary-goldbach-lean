import LiuWang.Proof.ExplicitPerron.HalfInteger
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The printed half-integer constants

These estimates retain the factor `2^b` in the lower central range.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ExplicitPerron

theorem log_lower_two {x : ℝ} (hx : 2 ≤ x) :
    2 / 3 + 2 * (x - 2) / (x + 2) ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have h := Real.le_log_one_add_of_nonneg (x := x / 2 - 1) (by linarith)
  rw [show 1 + (x / 2 - 1) = x / 2 by ring, Real.log_div hx0.ne' (by norm_num)] at h
  have heq : 2 * (x / 2 - 1) / (x / 2 - 1 + 2) = 2 * (x - 2) / (x + 2) := by
    apply (div_eq_div_iff (by linarith) (by linarith)).2
    ring
  rw [heq] at h
  linarith [Real.log_two_gt_d9]

theorem halfHarmonic_le_log_of_pos {m : ℕ} (hm : 1 ≤ m) :
    halfHarmonic m ≤ 3 + Real.log (m : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using halfHarmonic_le_log k

theorem source_lower_halfHarmonic {m : ℕ} (hm : 1 ≤ m) :
    Real.log 2 * halfHarmonic m ≤
      Real.log ((m : ℝ) + 1 / 2) + 3 / 2 - (1 / 2) / ((m : ℝ) + 1 / 2) := by
  by_cases hbig : 16 ≤ m
  · have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hbig
    have hm0 : (0 : ℝ) < m := by linarith
    have hlog : 8 / 3 ≤ Real.log ((m : ℝ) + 1 / 2) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
        (by linarith : (16 : ℝ) ≤ (m : ℝ) + 1 / 2)
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at h
      norm_num only [Nat.cast_ofNat] at h
      linarith [Real.log_two_gt_d9]
    have hH : halfHarmonic m ≤ 3 + Real.log ((m : ℝ) + 1 / 2) := by
      have h := Real.log_le_log hm0 (show (m : ℝ) ≤ (m : ℝ) + 1 / 2 by linarith)
      linarith [halfHarmonic_le_log_of_pos hm]
    have hdiv : (1 / 2 : ℝ) / ((m : ℝ) + 1 / 2) ≤ 1 / 8 := by
      exact (div_le_iff₀ (by positivity)).2 (by linarith)
    have hH0 : 0 ≤ halfHarmonic m := by unfold halfHarmonic; positivity
    calc
      _ ≤ (7 / 10 : ℝ) * (3 + Real.log ((m : ℝ) + 1 / 2)) :=
        mul_le_mul (by linarith [Real.log_two_lt_d9]) hH hH0 (by norm_num)
      _ ≤ _ := by linarith
  · by_cases hm1 : m = 1
    · subst m
      have h := Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
      norm_num [halfHarmonic, Finset.sum_range_succ] at h ⊢
      linarith [Real.log_two_lt_d9]
    · have hm2 : 2 ≤ m := by omega
      have h := log_lower_two (x := (m : ℝ) + 1 / 2)
        (by
          have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
          linarith)
      interval_cases m <;>
        norm_num [halfHarmonic, Finset.sum_range_succ] at h ⊢ <;>
        linarith [Real.log_two_lt_d9]

theorem source_upper_halfHarmonic {m : ℕ} (hm : 1 ≤ m) :
    Real.log 2 * halfHarmonic (m + 1) ≤
      Real.log ((m : ℝ) + 1 / 2) + Real.log 2 + 2 := by
  let x : ℝ := (m : ℝ) + 1 / 2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : 2 / 3 ≤ Real.log (2 * x) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by dsimp [x]; linarith : 2 ≤ 2 * x)
    linarith [Real.log_two_gt_d9]
  have hH : halfHarmonic (m + 1) ≤ 3 + Real.log (2 * x) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < m + 1)
      (show (m : ℝ) + 1 ≤ 2 * x by dsimp [x]; linarith)
    linarith [halfHarmonic_le_log m]
  have hH0 : 0 ≤ halfHarmonic (m + 1) := by unfold halfHarmonic; positivity
  calc
    _ ≤ (7 / 10 : ℝ) * (3 + Real.log (2 * x)) :=
      mul_le_mul (by linarith [Real.log_two_lt_d9]) hH hH0 (by norm_num)
    _ ≤ Real.log (2 * x) + 2 := by linarith
    _ = _ := by rw [Real.log_mul (by norm_num) hx.ne']; dsimp [x]; ring

end LiuWang.Proof.ExplicitPerron
