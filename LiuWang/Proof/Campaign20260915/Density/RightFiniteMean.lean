import LiuWang.Proof.Campaign20260915.Density.WeightedKernel

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

namespace LiuWang.Proof.Campaign20260915.Density

def rightTerm (y s : ℝ) (n : ℕ) : ℂ := LSeries.term (coefficient y) (s : ℂ) n

theorem norm_rightTerm (y s : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖rightTerm y s n‖ = ‖coefficient y n‖ * (n : ℝ) ^ (-s) := by
  rw [rightTerm, LSeries.norm_term_eq, if_neg hn.ne']
  simp only [Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem rightTerm_square (y d : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖rightTerm y (1 + d) n‖ ^ 2 =
      ‖coefficient y n‖ ^ 2 * (n : ℝ) ^ (-(2 + 2 * d)) := by
  rw [norm_rightTerm y _ hn, mul_pow]
  congr 1
  rw [pow_two, ← Real.rpow_add (Nat.cast_pos.mpr hn)]
  congr 1
  ring

theorem divisor_mass_square {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {s : ℝ} (hs : 1 < s) :
    (∑ n ∈ S, (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)) ^ 2 ≤
      (1 + 1 / (s - 1)) ^ 5 := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (f := fun n => (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s))
    (g := fun n => (n : ℝ) ^ (-s))
    (r := fun n => (n.divisors.card : ℝ) * (n : ℝ) ^ (-s))
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun _ _ => le_of_eq (by ring))
  have hb := mul_le_mul (divisor_square_power hS hs) (finite_power_sum S hs)
    (sum_nonneg (fun _ _ => by positivity)) (by positivity)
  exact hc.trans (hb.trans_eq (by ring))

theorem rightTerm_mass_square {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {y s : ℝ} (hy : 1 < y) (hs : 1 < s) :
    (∑ n ∈ S, ‖rightTerm y s n‖) ^ 2 ≤ (1 + 1 / (s - 1)) ^ 5 := by
  have hpoint (n : ℕ) (hn : n ∈ S) :
      ‖rightTerm y s n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (-s) := by
    rw [norm_rightTerm y s (hS n hn)]
    exact mul_le_mul_of_nonneg_right (coefficient_norm_le hy n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-s))
  have h := sum_le_sum hpoint
  exact (pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) h 2).trans
    (divisor_mass_square hS hs)

theorem rightTerm_log_moment {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {y d : ℝ} (hy : 1 < y) (hd : 0 < d) :
    (∑ n ∈ S, (n : ℝ) * ‖rightTerm y (1 + d) n‖ ^ 2 * (3 + Real.log n)) ≤
      3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4 := by
  apply le_trans (sum_le_sum (fun n hn => ?_)) (divisor_square_log_power hS hd)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hS n hn)
  have hlog : 0 ≤ 3 + Real.log n := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hS n hn)
    linarith
  have he : (n : ℝ) * ‖rightTerm y (1 + d) n‖ ^ 2 =
      ‖coefficient y n‖ ^ 2 * (n : ℝ) ^ (-(1 + 2 * d)) := by
    rw [rightTerm_square y d (hS n hn)]
    rw [show -(1 + 2 * d) = 1 + (-(2 + 2 * d)) by ring,
      Real.rpow_add hn0, Real.rpow_one]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (coefficient_norm_le hy n) 2)
      (Real.rpow_nonneg hn0.le _)) hlog

theorem right_finite_mean {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    {y d T : ℝ} (hy : 1 < y) (hd : 0 < d) (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖exponentialPolynomial S (rightTerm y (1 + d))
      (fun n => -Real.log n) t‖ ^ 2) ≤
      2 * T * ((24 / y) * y ^ (-2 * d)) +
      4 * (3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4) +
      4 * (1 + 1 / d) ^ 5 := by
  have hw : Set.InjOn (fun n : ℕ => -Real.log n) S := by
    intro m hm n hn he
    have hh := Real.log_injOn_pos
      (show (m : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < m; exact_mod_cast hS m hm)
      (show (n : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < n; exact_mod_cast hS n hn)
      (neg_injective he)
    exact_mod_cast hh
  have hm := finite_mean_le S (rightTerm y (1 + d)) (fun n => -Real.log n) hw hT
  have heq :
      (∑ m ∈ S, ∑ n ∈ S.erase m, ‖rightTerm y (1 + d) m‖ * ‖rightTerm y (1 + d) n‖ /
          |-Real.log m - -Real.log n|) ≤
      ∑ m ∈ S, ∑ n ∈ S, ‖rightTerm y (1 + d) m‖ * ‖rightTerm y (1 + d) n‖ /
          |Real.log m - Real.log n| := by
    have habs (m n : ℕ) :
        |-Real.log m - -Real.log n| = |Real.log m - Real.log n| := by
      rw [neg_sub_neg, abs_sub_comm]
    simp_rw [habs]
    exact sum_le_sum (fun _ _ => sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      (fun _ _ _ => by positivity))
  have hk := weighted_off_diagonal S hS (fun n => ‖rightTerm y (1 + d) n‖)
    (fun _ _ => norm_nonneg _)
  have hlog := rightTerm_log_moment hS hy hd
  have hmass := rightTerm_mass_square hS hy (show 1 < 1 + d by linarith)
  simp only [add_sub_cancel_left] at hmass
  have hdiag : (∑ n ∈ S, ‖rightTerm y (1 + d) n‖ ^ 2) ≤
      (24 / y) * y ^ (-2 * d) := by
    have he : (∑ n ∈ S, ‖rightTerm y (1 + d) n‖ ^ 2) =
        ∑ n ∈ S, ‖coefficient y n‖ ^ 2 * (n : ℝ) ^ (-(2 + 2 * d)) :=
      sum_congr rfl (fun n hn => rightTerm_square y d (hS n hn))
    rw [he]
    exact detector_right_diagonal hS hy.le hd.le
  have hdiag' := mul_le_mul_of_nonneg_left hdiag (show 0 ≤ 2 * T by positivity)
  linarith

#print axioms right_finite_mean

end LiuWang.Proof.Campaign20260915.Density
