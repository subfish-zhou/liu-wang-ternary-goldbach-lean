import LiuWang.Proof.SourceRoute.MajorOrdinary.SourceSums
import LiuWang.Proof.SingularSeries.Uniform.Mean

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

def totientRatioPower (s : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun q => (q : ℝ) ^ s * Uniform.ratioSquare q, by simp [Uniform.ratioSquare]⟩

theorem squareSum_totientRatioPower (P s : ℝ) :
    Uniform.squareSum (totientRatioPower s) ⌊P⌋₊ =
      ∑ q ∈ denominators P, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2 := by
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    have := (Finset.mem_Icc.mp hq).1
    omega)
  change ((q : ℝ) ^ s * ((q : ℝ) / (q.totient : ℝ)) ^ 2) / (q : ℝ) ^ 2 = _
  rw [div_pow]
  field_simp

theorem totientWeight_shift {q : ℕ} (hq : 0 < q) (s : ℝ) (j : ℕ) :
    totientWeight q (s + j) = totientWeight q s * (q : ℝ) ^ j := by
  simp only [totientWeight, Real.rpow_add (Nat.cast_pos.mpr hq), Real.rpow_natCast]
  ring

theorem quadratic_moment_expansion (P s a b : ℝ) :
    (∑ q ∈ denominators P, totientWeight q s * (a + b * (q : ℝ)) ^ 2) =
      a ^ 2 * totientMoment P s + 2 * a * b * totientMoment P (s + 1) +
        b ^ 2 * totientMoment P (s + 2) := by
  simp only [totientMoment, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  rw [show s + 1 = s + (1 : ℕ) by simp, totientWeight_shift hq0 s 1,
    show s + 2 = s + (2 : ℕ) by simp, totientWeight_shift hq0 s 2]
  ring

theorem cubic_moment_expansion (P s a b : ℝ) :
    (∑ q ∈ denominators P, ((q : ℝ) ^ s / (q.totient : ℝ) ^ 2) *
      (a + b * (q : ℝ)) ^ 3) =
      a ^ 3 * Uniform.squareSum (totientRatioPower s) ⌊P⌋₊ +
        3 * a ^ 2 * b * Uniform.squareSum (totientRatioPower (s + 1)) ⌊P⌋₊ +
        3 * a * b ^ 2 * Uniform.squareSum (totientRatioPower (s + 2)) ⌊P⌋₊ +
        b ^ 3 * Uniform.squareSum (totientRatioPower (s + 3)) ⌊P⌋₊ := by
  simp only [squareSum_totientRatioPower, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
  have hpow (j : ℕ) : (q : ℝ) ^ (s + j) = (q : ℝ) ^ s * (q : ℝ) ^ j := by
    rw [Real.rpow_add hq0, Real.rpow_natCast]
  rw [show s + 1 = s + (1 : ℕ) by simp, hpow 1,
    show s + 2 = s + (2 : ℕ) by simp, hpow 2,
    show s + 3 = s + (3 : ℕ) by simp, hpow 3]
  ring

theorem I13_expanded_moments {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    ‖I13 N‖ ≤ quadraticPrefactor * (N : ℝ) ^ 2 *
      (0.0194 ^ 2 * totientMoment (sourceP N) (1 / 3) +
        2 * 0.0194 * (0.063 / sourceL N ^ 3) * totientMoment (sourceP N) (4 / 3) +
        (0.063 / sourceL N ^ 3) ^ 2 * totientMoment (sourceP N) (7 / 3)) := by
  have he := quadratic_moment_expansion (sourceP N) (1 / 3) 0.0194 (0.063 / sourceL N ^ 3)
  norm_num only at he ⊢
  rw [← he, Finset.mul_sum]
  apply (I13_bound (exp_2000_le_of_exp_3100_le hN)).trans
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  have h := quadraticCost_le_source_sums (exp_2000_le_of_exp_3100_le hN)
    (hlow q hq) (hhigh q hq)
  norm_num only at h
  simpa only [mul_assoc] using h

theorem I14_expanded_moments {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    ‖I14 N‖ ≤ (3.36 / (5 * Real.pi)) * (N : ℝ) ^ 2 *
      (0.0194 ^ 3 * Uniform.squareSum (totientRatioPower (1 / 2)) ⌊sourceP N⌋₊ +
        3 * 0.0194 ^ 2 * (0.063 / sourceL N ^ 3) *
          Uniform.squareSum (totientRatioPower (3 / 2)) ⌊sourceP N⌋₊ +
        3 * 0.0194 * (0.063 / sourceL N ^ 3) ^ 2 *
          Uniform.squareSum (totientRatioPower (5 / 2)) ⌊sourceP N⌋₊ +
        (0.063 / sourceL N ^ 3) ^ 3 *
          Uniform.squareSum (totientRatioPower (7 / 2)) ⌊sourceP N⌋₊) := by
  have he := cubic_moment_expansion (sourceP N) (1 / 2) 0.0194 (0.063 / sourceL N ^ 3)
  norm_num only at he ⊢
  rw [← he, Finset.mul_sum]
  apply (I14_bound (exp_2000_le_of_exp_3100_le hN)).trans
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  have h := cubicCost_le_source_sums (exp_2000_le_of_exp_3100_le hN)
    (hlow q hq) (hhigh q hq)
  norm_num only at h
  simpa only [Real.sqrt_eq_rpow, mul_assoc] using h

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
