import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.SourceTailAssembly
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.Source423Scalar
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.ExpandedMoments
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

theorem source420_at_endpoint :
    nu 10000000000 ≤ (10000000000 : ℝ) ^ (0.080521 : ℝ) :=
  nu_le_source_power le_rfl

theorem first_tail_rectangle {s : ℝ} (hs : s ≤ 7 / 6) :
    nuKernel s 100001 ≤ ∫ x in (100000 : ℝ)..100001, nuKernel s x := by
  simpa only [show (100000 + 1 : ℕ) = 100001 by omega,
    Finset.Icc_self, Finset.sum_singleton, Nat.cast_ofNat] using
    nuKernel_sum_le_integral hs (m := 100000) (b := 100001) le_rfl (by omega)

theorem empty_tail_at_split (s : ℝ) :
    (∑ q ∈ Finset.Icc (100001 : ℕ) 100000, nuKernel s q) = 0 := by
  rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]

theorem high_tail_at_split :
    (∫ x in (10000000000 : ℝ)..10000000000, nuKernel (7 / 6) x) =
      nu 10000000000 ^ 2 * 6 *
        ((10000000000 : ℝ) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) := by
  rw [intervalIntegral.integral_same, ten_billion_sixth_root, sub_self, mul_zero]

theorem nonsquarefree_quadratic_weight :
    totientWeight 4 (1 / 3) = 0 := by
  norm_num [totientWeight, ArithmeticFunction.moebius]
  intro h
  exact (Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two) (by norm_num)

theorem nonsquarefree_cubic_weight_positive :
    (0 : ℝ) < (4 : ℝ) ^ (1 / 2 : ℝ) / (Nat.totient 4 : ℝ) ^ 2 := by
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
