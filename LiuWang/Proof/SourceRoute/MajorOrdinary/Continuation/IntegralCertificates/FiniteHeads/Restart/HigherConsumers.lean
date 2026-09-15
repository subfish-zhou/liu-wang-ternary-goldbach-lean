import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.CubicArithmetic

set_option autoImplicit false
noncomputable section
open Finset
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularSeries.Uniform

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

theorem quadratic_secant {a b t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (a + b * t) ^ 2 ≤ a ^ 2 + ((a + b) ^ 2 - a ^ 2) * t := by
  nlinarith only [mul_nonneg (sq_nonneg b) (mul_nonneg ht (sub_nonneg.mpr ht1))]

theorem cubic_secant {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (a + b * t) ^ 3 ≤ a ^ 3 + ((a + b) ^ 3 - a ^ 3) * t := by
  have h : 0 ≤ b ^ 2 * (t * (1 - t)) * (3 * a + b * (1 + t)) :=
    mul_nonneg (mul_nonneg (sq_nonneg b) (mul_nonneg ht (sub_nonneg.mpr ht1)))
      (by positivity)
  nlinarith only [h]

theorem unweighted_linear_sum (P s a b : ℝ) :
    (∑ q ∈ denominators P, ((q : ℝ) ^ s / (q.totient : ℝ) ^ 2) *
      (a + b * (q : ℝ))) =
      a * squareSum (totientRatioPower s) ⌊P⌋₊ +
        b * squareSum (totientRatioPower (s + 1)) ⌊P⌋₊ := by
  simp only [squareSum_totientRatioPower, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  rw [Real.rpow_add (Nat.cast_pos.mpr (mem_Icc.mp hq).1), Real.rpow_one]
  ring

theorem cubic_mother_payment {P : ℝ} (hP : 10000000000 ≤ P) :
    (∑ q ∈ denominators P, ((q : ℝ) ^ (1 / 2 : ℝ) / (q.totient : ℝ) ^ 2) *
      (0.0194 + (0.063 / P) * (q : ℝ)) ^ 3) ≤
      0.0194 ^ 3 * 12.4 + ((0.0194 + 0.063) ^ 3 - 0.0194 ^ 3) * 0.000207 := by
  have hp : 0 < P := by linarith
  calc
    _ ≤ ∑ q ∈ denominators P, ((q : ℝ) ^ (1 / 2 : ℝ) / (q.totient : ℝ) ^ 2) *
        (0.0194 ^ 3 + (((0.0194 + 0.063) ^ 3 - 0.0194 ^ 3) / P) * (q : ℝ)) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hqP : (q : ℝ) / P ≤ 1 :=
        (div_le_one hp).mpr ((Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le hp.le))
      have h := cubic_secant (a := 0.0194) (b := 0.063) (by norm_num) (by norm_num)
        (div_nonneg (Nat.cast_nonneg q) hp.le) hqP
      convert! h using 1 <;> ring
    _ = 0.0194 ^ 3 * squareSum (totientRatioPower (1 / 2)) ⌊P⌋₊ +
        ((0.0194 + 0.063) ^ 3 - 0.0194 ^ 3) *
          (squareSum (totientRatioPower (3 / 2)) ⌊P⌋₊ / P) := by
      rw [unweighted_linear_sum]
      norm_num only
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (unweighted_half_moment (by linarith)) (by norm_num))
      (mul_le_mul_of_nonneg_left (unweighted_three_halves_normalized hP) (by norm_num))

theorem cubic_expanded_mothers_paid {P : ℝ} (hP : 10000000000 ≤ P) :
    0.0194 ^ 3 * squareSum (totientRatioPower (1 / 2)) ⌊P⌋₊ +
      3 * 0.0194 ^ 2 * (0.063 / P) *
        squareSum (totientRatioPower (3 / 2)) ⌊P⌋₊ +
      3 * 0.0194 * (0.063 / P) ^ 2 *
        squareSum (totientRatioPower (5 / 2)) ⌊P⌋₊ +
      (0.063 / P) ^ 3 * squareSum (totientRatioPower (7 / 2)) ⌊P⌋₊ ≤
        0.0194 ^ 3 * 12.4 + ((0.0194 + 0.063) ^ 3 - 0.0194 ^ 3) * 0.000207 := by
  have he := cubic_moment_expansion P (1 / 2) 0.0194 (0.063 / P)
  norm_num only at he ⊢
  rw [← he]
  convert! cubic_mother_payment hP using 1 <;> norm_num

theorem cubic_prefactor_le : (3.36 / (5 * Real.pi) : ℝ) ≤ 0.214 := by
  have hp := Real.pi_gt_d6.le
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  linarith

theorem I14_no_RS {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    ‖I14 N‖ ≤ 0.00002 * (N : ℝ) ^ 2 := by
  have hm := cubic_expanded_mothers_paid (sourceP_ge_ten_billion hN)
  have hbase := I14_expanded_moments hN hlow hhigh
  have hscalar : (3.36 / (5 * Real.pi)) *
      (0.0194 ^ 3 * 12.4 + ((0.0194 + 0.063) ^ 3 - 0.0194 ^ 3) * 0.000207) ≤ 0.00002 := by
    exact (mul_le_mul_of_nonneg_right cubic_prefactor_le (by norm_num)).trans (by norm_num)
  unfold sourceP at hm
  apply hbase.trans
  apply (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (3.36 / (5 * Real.pi)) * (N : ℝ) ^ 2)).trans
  convert! mul_le_mul_of_nonneg_right hscalar (sq_nonneg (N : ℝ)) using 1
  ring

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart
