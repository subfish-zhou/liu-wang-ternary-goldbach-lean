import LiuWang.Proof.WeightedHighZeros.Continuation.Scalar

/-!
# Paying the `beta = 19/20` capped contribution at `exp(3100)`

The capped sum includes all high-height zeros, not just those to the left
of `19/20`. Thus the exact complementary excess has no missing base mass.
No high-alpha density estimate is an input to this payment.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation

def capWeight (N : ℕ) (rho : ℂ) : ℝ :=
  min ((N : ℝ) ^ (rho.re - 1)) ((N : ℝ) ^ (-1 / 20 : ℝ))

def cappedHighSum (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ highValues N chi,
    (analyticOrderNatAt chi.LFunction rho : ℝ) * (capWeight N rho / |rho.im|)

def excessHighSum (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ (highValues N chi).filter (fun rho => 19 / 20 < rho.re),
    (analyticOrderNatAt chi.LFunction rho : ℝ) *
      (((N : ℝ) ^ (rho.re - 1) - (N : ℝ) ^ (-1 / 20 : ℝ)) / |rho.im|)

theorem capWeight_eq_source_power {N : ℕ} (hN : 1 ≤ N) (rho : ℂ) :
    capWeight N rho = (N : ℝ) ^ (min rho.re (19 / 20) - 1) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hr : rho.re ≤ 19 / 20
  · have hh : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    rw [capWeight, min_eq_left hh, min_eq_left hr]
  · have hh : (N : ℝ) ^ (-1 / 20 : ℝ) ≤ (N : ℝ) ^ (rho.re - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    rw [capWeight, min_eq_right hh, min_eq_right (le_of_not_ge hr)]
    norm_num

theorem cap_level_eq_exp {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (-1 / 20 : ℝ) = Real.exp (-sourceL N / 20) := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hN)]
  congr 1
  unfold sourceL
  ring

theorem cappedHighSum_nonneg (N q : ℕ) [NeZero q] :
    0 ≤ cappedHighSum N q := by
  apply Finset.sum_nonneg
  intro chi _
  apply Finset.sum_nonneg
  intro rho _
  unfold capWeight
  positivity

theorem excessHighSum_nonneg {N q : ℕ} [NeZero q] (hN : 1 ≤ N) :
    0 ≤ excessHighSum N q := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply Finset.sum_nonneg
  intro chi _
  apply Finset.sum_nonneg
  intro rho hrho
  have hh : (N : ℝ) ^ (-1 / 20 : ℝ) ≤ (N : ℝ) ^ (rho.re - 1) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith [(Finset.mem_filter.mp hrho).2])
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sub_nonneg.mpr hh) (abs_nonneg _))

theorem highSum_eq_capped_add_excess {N q : ℕ} [NeZero q] (hN : 1 ≤ N) :
    highSum N q = cappedHighSum N q + excessHighSum N q := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  symm
  unfold cappedHighSum excessHighSum
  rw [← Finset.sum_add_distrib]
  change _ = ∑ chi : Character q, ∑ rho ∈ highValues N chi,
    (analyticOrderNatAt chi.LFunction rho : ℝ) * ((N : ℝ) ^ (rho.re - 1) / |rho.im|)
  apply Finset.sum_congr rfl
  intro chi _
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hr : 19 / 20 < rho.re
  · have hh : (N : ℝ) ^ (-1 / 20 : ℝ) ≤ (N : ℝ) ^ (rho.re - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    rw [if_pos hr, capWeight, min_eq_right hh]
    ring
  · have hh : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    rw [if_neg hr, capWeight, min_eq_left hh, add_zero]

theorem cappedHighSum_le_reciprocal (N q : ℕ) [NeZero q] :
    cappedHighSum N q ≤ (N : ℝ) ^ (-1 / 20 : ℝ) *
      bandSum 1 q (omegaCutoff N q) (sourceT N) := by
  calc
    _ ≤ ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((N : ℝ) ^ (-1 / 20 : ℝ) / |rho.im|) := by
      exact Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ =>
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (min_le_right _ _) (abs_nonneg _)) (Nat.cast_nonneg _)))
    _ = _ := by
      simp only [bandSum, highValues, Nat.cast_one, Real.one_rpow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      apply Finset.sum_congr rfl
      intro rho _
      ring

theorem cappedHighSum_le_original_threshold {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    cappedHighSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hs := (cappedHighSum_le_reciprocal N q).trans
    (mul_le_mul_of_nonneg_left (actual_reciprocal_le hN hq) (by positivity))
  rw [cap_level_eq_exp hn] at hs
  have hp := mul_le_mul_of_nonneg_right
    (capped_scalar_payment (Parameters.sourceL_ge_3100 hN)) (Nat.cast_nonneg q)
  exact hs.trans (by convert hp using 1 <;> ring)

theorem original_threshold_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) + excessHighSum N q := by
  rw [highSum_eq_capped_add_excess (Parameters.nat_pos_of_exp_le hN)]
  exact add_le_add (cappedHighSum_le_original_threshold hN hq) le_rfl

theorem primed_original_threshold_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤
      Real.exp (-75) * q / sourceL N ^ (4 : ℕ) + excessHighSum N q := by
  rw [primedHighSum_eq_highSum hN he]
  exact original_threshold_reduction hN hq

end LiuWang.Proof.WeightedHighZeros.Continuation
