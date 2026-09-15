import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalPrefix
import Mathlib.Algebra.BigOperators.Module

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem weighted_prefix_lower (a w : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C : ℝ}
    (hprefix : ∀ n, 1 ≤ n → n ≤ N → C ≤ ∑ j ∈ range n, a j)
    (hw : ∀ j < N, 0 ≤ w j)
    (hmono : ∀ j, j + 1 < N → w (j + 1) ≤ w j) :
    C * w 0 ≤ ∑ j ∈ range N, w j * a j := by
  have hid := sum_range_by_parts w a N
  simp only [smul_eq_mul] at hid
  rw [hid]
  have hlast := mul_le_mul_of_nonneg_left (hprefix N hN le_rfl) (hw (N - 1) (by omega))
  have hsum : (∑ j ∈ range (N - 1), (w (j + 1) - w j) * ∑ i ∈ range (j + 1), a i) ≤
      ∑ j ∈ range (N - 1), (w (j + 1) - w j) * C := by
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonpos_left (hprefix (j + 1) (by omega) (by have := mem_range.mp hj; omega))
      (sub_nonpos.mpr (hmono j (by have := mem_range.mp hj; omega)))
  rw [← sum_mul, sum_range_sub] at hsum
  nlinarith

def horizontalPoint (sigma : ℝ) : ℂ := ⟨sigma, 16⟩

theorem horizontal_cpow (sigma : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-horizontalPoint sigma) =
      (((n : ℝ) ^ (1 / 2 - sigma) : ℝ) : ℂ) * (n : ℂ) ^ (-criticalPoint 16) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast,
    ← cpow_add _ _ hn0]
  congr 1
  apply Complex.ext <;> norm_num [horizontalPoint, criticalPoint]
  ring

theorem horizontal_partial_sum_lower {sigma : ℝ} (hs : 1 / 2 ≤ sigma) :
    (1 / 3 : ℝ) ≤ (zetaPartialSum (horizontalPoint sigma) 64).re := by
  let a : ℕ → ℝ := fun j => (((j + 1 : ℕ) : ℂ) ^ (-criticalPoint 16)).re
  let w : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ (1 / 2 - sigma)
  have hp (n : ℕ) (hn : 1 ≤ n) (hN : n ≤ 64) : (1 / 3 : ℝ) ≤ ∑ j ∈ range n, a j := by
    simpa [a, zetaPartialSum, re_sum] using horizontal_prefix_real hn hN
  have hw (j : ℕ) (_ : j < 64) : 0 ≤ w j := Real.rpow_nonneg (by positivity) _
  have hm (j : ℕ) (_ : j + 1 < 64) : w (j + 1) ≤ w j :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by norm_cast; omega) (by linarith)
  have h := weighted_prefix_lower a w (N := 64) (by norm_num) hp hw hm
  have he : (zetaPartialSum (horizontalPoint sigma) 64).re = ∑ j ∈ range 64, w j * a j := by
    rw [zetaPartialSum, re_sum]
    apply sum_congr rfl
    intro j _
    have h := horizontal_cpow sigma (n := j + 1) (by omega)
    push_cast at h
    rw [h, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    simp only [a, w, Nat.cast_add, Nat.cast_one]
  rw [he]
  simpa [w] using h

#print axioms horizontal_partial_sum_lower

end LiuWang.Proof.Campaign20260915.ZetaValidation
