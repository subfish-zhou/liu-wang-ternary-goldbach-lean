import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

/-! Finite-family positive Gram kernels and the Heath-Brown counting step.
The index type need not inject into zero values: repeated zeros remain distinct. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical

namespace LiuWang.Proof.NearOneDensity

def gram {ι : Type*} (s : Finset ι) (v : ι → ℂ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, (v i * conj (v j)).re

theorem gram_eq_sq {ι : Type*} (s : Finset ι) (v : ι → ℂ) :
    gram s v = (∑ i ∈ s, (v i).re) ^ 2 + (∑ i ∈ s, (v i).im) ^ 2 := by
  simp only [gram, Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg,
    sub_neg_eq_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem gram_nonneg {ι : Type*} (s : Finset ι) (v : ι → ℂ) :
    0 ≤ gram s v := by
  rw [gram_eq_sq]
  positivity

theorem re_sum_sq_le_gram {ι : Type*} (s : Finset ι) (v : ι → ℂ) :
    (∑ i ∈ s, (v i).re) ^ 2 ≤ gram s v := by
  rw [gram_eq_sq]
  nlinarith [sq_nonneg (∑ i ∈ s, (v i).im)]

theorem weighted_quadratic {ι ν : Type*} (s : Finset ι) (u : Finset ν)
    (w : ν → ℝ) (v : ι → ν → ℂ) (hw : ∀ n ∈ u, 0 ≤ w n) :
    (∑ i ∈ s, ∑ n ∈ u, w n * (v i n).re) ^ 2 ≤
      (∑ n ∈ u, w n) * ∑ i ∈ s, ∑ j ∈ s,
        ∑ n ∈ u, w n * (v i n * conj (v j n)).re := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul u hw
    (fun n hn => mul_nonneg (hw n hn) (gram_nonneg s (fun i => v i n)))
    (r := fun n => w n * ∑ i ∈ s, (v i n).re)
    (fun n hn => by
      calc
        (w n * ∑ i ∈ s, (v i n).re) ^ 2 =
            (w n) ^ 2 * (∑ i ∈ s, (v i n).re) ^ 2 := mul_pow _ _ _
        _ ≤ (w n) ^ 2 * gram s (fun i => v i n) :=
          mul_le_mul_of_nonneg_left (re_sum_sq_le_gram s _) (sq_nonneg _)
        _ = w n * (w n * gram s (fun i => v i n)) := by ring)
  have hleft : (∑ i ∈ s, ∑ n ∈ u, w n * (v i n).re) =
      ∑ n ∈ u, w n * ∑ i ∈ s, (v i n).re := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hright : (∑ n ∈ u, w n * gram s (fun i => v i n)) =
      ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ u, w n * (v i n * conj (v j n)).re := by
    simp only [gram, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hleft, ← hright]
  exact h

theorem pair_sum_le {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ) (A B : ℝ)
    (hdiag : ∀ i ∈ s, K i i ≤ A)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → K i j ≤ B) :
    (∑ i ∈ s, ∑ j ∈ s, K i j) ≤
      A * s.card + B * ((s.card : ℝ) ^ 2 - s.card) := by
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, if i = j then A else B := by
      gcongr with i hi j hj
      split_ifs with hij
      · subst j; exact hdiag i hi
      · exact hoff i hi j hj hij
    _ = A * s.card + B * ((s.card : ℝ) ^ 2 - s.card) := by
      have hrow : ∀ i ∈ s, (∑ j ∈ s, if i = j then A else B) =
          A + ((s.card : ℝ) - 1) * B := by
        intro i hi
        rw [← Finset.sum_erase_add _ _ hi]
        simp only [ite_true]
        have hc : ((s.erase i).card : ℝ) = (s.card : ℝ) - 1 := by
          have hh : ((s.erase i).card : ℝ) + 1 = s.card := by
            exact_mod_cast Finset.card_erase_add_one hi
          linarith
        have he : (∑ j ∈ s.erase i, if i = j then A else B) =
            ((s.erase i).card : ℝ) * B := by
          calc
            _ = ∑ _j ∈ s.erase i, B := Finset.sum_congr rfl
              (fun j hj => if_neg (Finset.mem_erase.mp hj).1.symm)
            _ = _ := by simp
        rw [he, hc]
        ring
      rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
      ring

theorem heath_brown_count {N : ℕ} {A B D F : ℝ}
    (hA : 0 ≤ A) (hBA : B ≤ A) (hD : 0 ≤ D) (hF : F ≤ -D * N)
    (hquad : F ^ 2 ≤ A * (A * N + B * ((N : ℝ) ^ 2 - N)))
    (hgap : 0 < D ^ 2 - A * B) :
    (N : ℝ) ≤ (A ^ 2 - A * B) / (D ^ 2 - A * B) := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hlow : (D * N) ^ 2 ≤ F ^ 2 := by
    have : D * N ≤ -F := by linarith
    nlinarith [mul_nonneg hD hN]
  by_cases hz : N = 0
  · subst N
    simp only [Nat.cast_zero]
    exact div_nonneg (by nlinarith [mul_nonneg hA (sub_nonneg.mpr hBA)]) hgap.le
  · have hpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    apply (le_div_iff₀ hgap).mpr
    have hprod : (N : ℝ) * ((N : ℝ) * (D ^ 2 - A * B) -
        (A ^ 2 - A * B)) ≤ 0 := by nlinarith [hquad]
    have hh : (N : ℝ) * (D ^ 2 - A * B) - (A ^ 2 - A * B) ≤ 0 := by
      by_contra! h
      exact (not_lt_of_ge hprod) (mul_pos hpos h)
    linarith

end LiuWang.Proof.NearOneDensity
