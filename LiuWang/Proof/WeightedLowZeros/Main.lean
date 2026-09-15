import LiuWang.Proof.WeightedLowZeros.Weight
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

/-!
# Unconditional mother bounds on the actual closed low-height sum

No zero is removed here. The smoothing parameter and conductor-sensitive
minimum are retained. A real-part cap is a pointwise input, not a weighted-sum
assumption; the uncapped theorem discharges it from the actual zero window.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedLowZeros

def weightedSum {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (y : ℝ) : ℝ :=
  ∑ rho ∈ CompleteExpansion.zeroValues chi y, (zeroMultiplicity chi rho : ℝ) * weight N rho.re

def lowSum (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q, weightedSum N chi (omegaCutoff N q)

def countMother (q : ℕ) [NeZero q] (y a : ℝ) : ℝ :=
  ∑ chi : Character q, sharpenedBound chi y a

theorem weightedSum_nonneg {N q : ℕ} [NeZero q] (chi : Character q) (y : ℝ) :
    0 ≤ weightedSum N chi y :=
  Finset.sum_nonneg fun _ hr => mul_nonneg (Nat.cast_nonneg _)
    (weight_nonneg N (CompleteExpansion.mem_zeroValues.mp hr).2.1)

theorem subset_weighted_le {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    (chi : Character q) {y a sigma : ℝ} (hy : 0 ≤ y) (ha : 0 < a) (hs : 0 < sigma)
    (Z : Finset ℂ) (hZ : Z ⊆ CompleteExpansion.zeroValues chi y)
    (hcap : ∀ rho ∈ Z, rho.re ≤ sigma) :
    (∑ rho ∈ Z, (zeroMultiplicity chi rho : ℝ) * weight N rho.re) ≤
      weight N sigma * sharpenedBound chi y a := by
  calc
    _ ≤ ∑ rho ∈ Z, (zeroMultiplicity chi rho : ℝ) * weight N sigma :=
      Finset.sum_le_sum fun rho hr => mul_le_mul_of_nonneg_left
        (weight_mono hN (CompleteExpansion.mem_zeroValues.mp (hZ hr)).2.1 (hcap rho hr))
        (Nat.cast_nonneg _)
    _ ≤ ∑ rho ∈ CompleteExpansion.zeroValues chi y,
        (zeroMultiplicity chi rho : ℝ) * weight N sigma :=
      Finset.sum_le_sum_of_subset_of_nonneg hZ
        (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (weight_nonneg N hs))
    _ = weight N sigma * count chi (1 / 2) y := by
      rw [Applications.count_half_eq_complete]
      simp only [Nat.cast_sum, Finset.mul_sum, zeroMultiplicity, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (count_le_sharpenedBound chi (1 / 2) hy ha)
      (weight_nonneg N hs)

theorem weightedSum_le {N q : ℕ} [NeZero q] (hN : 1000 ≤ (N : ℝ))
    (chi : Character q) {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    weightedSum N chi y ≤ 0.999 * sharpenedBound chi y a := by
  simpa only [weightedSum, weight_one] using
    subset_weighted_le hN chi hy ha (by norm_num : (0 : ℝ) < 1)
      (CompleteExpansion.zeroValues chi y) (fun _ h => h)
      (fun _ hr => (CompleteExpansion.mem_zeroValues.mp hr).2.2.1.le)

theorem lowSum_le_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {a : ℝ} (ha : 0 < a) :
    lowSum N q ≤ 0.999 * countMother q (omegaCutoff N q) a := by
  have hy : 0 ≤ omegaCutoff N q :=
    le_trans (by norm_num) (Parameters.omegaCutoff_ge (NeZero.pos q) hq)
  simpa only [lowSum, countMother, Finset.mul_sum] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
      (fun chi _ => weightedSum_le (source_endpoint_ge_thousand hN) chi hy ha)

theorem countMother_le_family (q : ℕ) [NeZero q] (y a : ℝ) :
    countMother q y a ≤ familyBound q y :=
  sharpened_family_le_mother q y a

theorem countMother_nonneg (q : ℕ) [NeZero q] {y a : ℝ}
    (hy : 0 ≤ y) (ha : 0 < a) : 0 ≤ countMother q y a :=
  Finset.sum_nonneg fun chi _ => sharpenedBound_nonneg chi hy ha

theorem subset_Jrho_le {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) (y eta : ℝ) (Z : Finset ℂ)
    (hZ : Z ⊆ CompleteExpansion.zeroValues chi y) :
    (∑ rho ∈ Z, (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
      (N : ℝ) * ∑ rho ∈ Z, (zeroMultiplicity chi rho : ℝ) * weight N rho.re := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hr
  have h := mul_le_mul_of_nonneg_left
    (Jrho_le_weight hN (CompleteExpansion.mem_zeroValues.mp (hZ hr)).2.1 eta)
    (Nat.cast_nonneg (zeroMultiplicity chi rho) : (0 : ℝ) ≤ zeroMultiplicity chi rho)
  convert h using 1
  ring

theorem norm_subset_Jrho_le {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) (y eta : ℝ) (Z : Finset ℂ)
    (hZ : Z ⊆ CompleteExpansion.zeroValues chi y) :
    ‖∑ rho ∈ Z, (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta‖ ≤
      (N : ℝ) * ∑ rho ∈ Z, (zeroMultiplicity chi rho : ℝ) * weight N rho.re := by
  apply (norm_sum_le _ _).trans
  simpa only [norm_mul, Complex.norm_natCast] using subset_Jrho_le hN chi y eta Z hZ

theorem low_Jrho_le_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {a : ℝ} (ha : 0 < a) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
        (N : ℝ) * (0.999 * countMother q (omegaCutoff N q) a) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => subset_Jrho_le (Parameters.nat_pos_of_exp_le hN) chi
      (omegaCutoff N q) eta (CompleteExpansion.zeroValues chi (omegaCutoff N q)) (fun _ h => h))
  rw [← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left (lowSum_le_mother hN hq ha) (Nat.cast_nonneg _))

end LiuWang.Proof.WeightedLowZeros
