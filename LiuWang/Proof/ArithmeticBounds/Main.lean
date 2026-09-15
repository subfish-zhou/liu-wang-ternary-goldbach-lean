import LiuWang.Proof.Interfaces.Main
import LiuWang.Proof.ArithmeticBounds.FiniteSumCertificate

/-!
# Effective arithmetic bounds for Liu--Wang

This module proves the finite numerical estimate immediately following (4.5).
Each squarefree term is bounded by an integer multiple of `1 / 10000`, using
Euler's totient product formula and kernel-checked blocks of fifty integers.
No estimate for the remaining tail or the Rosser--Schoenfeld bound is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds

open scoped BigOperators

theorem moebius_totient_square_le_rounded (q : Nat) (hq : 0 < q) :
    |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
        (q.totient : Real) ^ 2 ≤ (roundedSquareWeight q : Real) / 10000 := by
  by_cases hs : Squarefree q
  · have hmu : |(ArithmeticFunction.moebius q : Real)| = 1 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs]
      norm_num
    have hden : 0 < q.totient ^ 2 := pow_pos (Nat.totient_pos.mpr hq) _
    have hround := (Nat.lt_mul_div_succ (10000 * q ^ 2) hden).le
    have hroundR :
        (10000 : Real) * (q : Real) ^ 2 ≤
          (q.totient : Real) ^ 2 * ((10000 * q ^ 2 / q.totient ^ 2 + 1 : Nat) : Real) := by
      exact_mod_cast hround
    rw [hmu, one_mul, roundedSquareWeight, if_pos hs, certificateTotient_eq]
    have hdenR : (0 : Real) < (q.totient : Real) ^ 2 := by positivity
    apply (div_le_div_iff₀ hdenR (by norm_num : (0 : Real) < 10000)).mpr
    nlinarith [hroundR]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    simp [roundedSquareWeight, hs]

/-- The certified finite head is slightly stronger than the source's `1961`. -/
theorem sum_moebius_totient_square_le_98039_div_50 :
    (∑ q ∈ Finset.Icc 1 1000,
      |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
        (q.totient : Real) ^ 2) ≤ 98039 / 50 := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 1000, (roundedSquareWeight q : Real) / 10000 :=
      Finset.sum_le_sum fun q hq =>
        moebius_totient_square_le_rounded q (Finset.mem_Icc.mp hq).1
    _ = ((∑ q ∈ Finset.Icc 1 1000, roundedSquareWeight q : Nat) : Real) / 10000 := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ ≤ (19607800 : Real) / 10000 := by
      gcongr
      exact_mod_cast roundedSquareWeight_sum_le
    _ = 98039 / 50 := by norm_num

/-- The literal finite numerical bound following Liu--Wang (4.5). -/
theorem sum_moebius_totient_square_le_1961 :
    (∑ q ∈ Finset.Icc 1 1000,
      |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
        (q.totient : Real) ^ 2) ≤ 1961 :=
  sum_moebius_totient_square_le_98039_div_50.trans (by norm_num)

/-- The finite head budget also applies to an arbitrary shorter cutoff. -/
theorem sum_moebius_totient_square_le_1961_of_le
    (X : Nat) (hX : X ≤ 1000) :
    (∑ q ∈ Finset.Icc 1 X,
      |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
        (q.totient : Real) ^ 2) ≤ 1961 := by
  refine le_trans ?_ sum_moebius_totient_square_le_1961
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hX)
  intro q _ _
  positivity

/-- Only the certified head is paid here; the source `P`-tail remains explicit. -/
theorem sum_moebius_totient_square_sourceP_le (N : Nat) :
    (∑ q ∈ Finset.Icc 1 ⌊Interfaces.sourceP N⌋₊,
      |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
        (q.totient : Real) ^ 2) ≤
      1961 + ∑ q ∈ Finset.Icc 1001 ⌊Interfaces.sourceP N⌋₊,
        |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
          (q.totient : Real) ^ 2 := by
  let X := ⌊Interfaces.sourceP N⌋₊
  have hsubset : Finset.Icc 1 X ⊆ Finset.Icc 1 1000 ∪ Finset.Icc 1001 X := by
    intro q hq
    simp only [Finset.mem_Icc, Finset.mem_union] at *
    omega
  have hdisjoint : Disjoint (Finset.Icc 1 1000) (Finset.Icc 1001 X) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_Icc] at *
    omega
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 1000 ∪ Finset.Icc 1001 X,
        |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
          (q.totient : Real) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q _ _
      positivity
    _ = (∑ q ∈ Finset.Icc 1 1000,
        |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
          (q.totient : Real) ^ 2) +
        ∑ q ∈ Finset.Icc 1001 X,
          |(ArithmeticFunction.moebius q : Real)| * (q : Real) ^ 2 /
            (q.totient : Real) ^ 2 := Finset.sum_union hdisjoint
    _ ≤ _ := by
      exact add_le_add sum_moebius_totient_square_le_1961 le_rfl

end LiuWang.Proof.ArithmeticBounds
