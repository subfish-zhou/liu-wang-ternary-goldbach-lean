import LiuWang.Proof.DirichletZeroCount.Remainder.SourceGamma
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # A uniform disk for every ordinary L-function to the right of two -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem square_tail_le : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) ≤ 3 / 4 := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ht := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 2).mpr hsum
  have ha : AntitoneOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ici (2 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
      (fun _ hx => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx)
  have hb := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-2 : ℝ))
    2 ha (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num : (0 : ℝ) < 2))
    (fun t ht => Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ ((2 : ℕ) : ℝ)) (le_of_lt ht)) _)
  simp only [Nat.cast_ofNat] at hb
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 2)] at hb
  rw [ht.tsum_eq_zero_add]
  norm_num [Real.rpow_neg, Real.rpow_two, Nat.add_assoc] at hb ⊢
  linarith

theorem norm_LFunction_sub_one_le {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 2 ≤ s.re) : ‖chi.LFunction s - 1‖ ≤ 3 / 4 := by
  have hs1 : 1 < s.re := by linarith
  have hsum := chi.LSeriesSummable_of_one_lt_re hs1
  have ht := (summable_nat_add_iff (f := LSeries.term (fun n : ℕ => chi n) s) 2).mpr hsum
  have he : chi.LFunction s - 1 =
      ∑' n : ℕ, LSeries.term (fun m : ℕ => chi m) s (n + 2) := by
    rw [chi.LFunction_eq_LSeries hs1]
    have hx := hsum.sum_add_tsum_nat_add 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, LSeries.term_zero,
      zero_add, LSeries.term_of_ne_zero (by norm_num : (1 : ℕ) ≠ 0),
      Nat.cast_one, map_one, one_cpow, div_one] at hx
    change (∑' n, LSeries.term (fun m : ℕ => chi m) s n) - 1 = _
    rw [← hx]
    ring
  have hm (n : ℕ) :
      ‖LSeries.term (fun m : ℕ => chi m) s (n + 2)‖ ≤ ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
    rw [LSeries.term_of_ne_zero (by omega), norm_div,
      norm_natCast_cpow_of_re_ne_zero (n + 2) (by linarith)]
    calc
      ‖chi ((n + 2 : ℕ) : ZMod q)‖ / ((n + 2 : ℕ) : ℝ) ^ s.re
          ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right (chi.norm_le_one _) (Real.rpow_nonneg (by positivity) _)
      _ = ((n + 2 : ℕ) : ℝ) ^ (-s.re) := by
        rw [Real.rpow_neg (by positivity), one_div]
      _ ≤ ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (by linarith)
  rw [he]
  exact (norm_tsum_le_tsum_norm ht.norm).trans
    ((ht.norm.tsum_le_tsum hm
      ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 2).mpr
        (Real.summable_nat_rpow.mpr (by norm_num)))).trans square_tail_le)

theorem LFunction_re_pos {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 2 ≤ s.re) : 0 < (chi.LFunction s).re := by
  have h := (neg_norm_le_re (chi.LFunction s - 1))
  have hb := norm_LFunction_sub_one_le chi hs
  simp only [sub_re, one_re] at h
  linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
