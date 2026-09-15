import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.SourceMoments

set_option autoImplicit false
noncomputable section
open Finset
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularSeries.Uniform

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

theorem sqrt_tangent_two {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ (x + 4) / 4 := by
  nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt x - 2)]

theorem small_rational_head :
    (∑ q ∈ Icc 1 (25 : ℕ), ((q : ℚ) + 4) / (4 * (q.totient : ℚ) ^ 2)) ≤ 6.2 := by
  norm_num [sum_Icc_succ_top, Nat.totient, Nat.Coprime, Finset.range_add_one,
    Finset.filter_insert, Finset.filter_singleton]

theorem unweighted_small_head :
    (∑ q ∈ Icc 1 (25 : ℕ), (q : ℝ) ^ (1 / 2 : ℝ) / (q.totient : ℝ) ^ 2) ≤ 6.2 := by
  calc
    _ ≤ ∑ q ∈ Icc 1 (25 : ℕ), ((q : ℝ) + 4) / (4 * (q.totient : ℝ) ^ 2) := by
      apply sum_le_sum
      intro q _
      rw [← Real.sqrt_eq_rpow]
      have h := div_le_div_of_nonneg_right (sqrt_tangent_two (Nat.cast_nonneg q))
        (sq_nonneg (q.totient : ℝ))
      convert! h using 1
      ring
    _ ≤ _ := by
      have h := (Rat.cast_le (K := ℝ)).mpr small_rational_head
      push_cast at h
      exact h

theorem unweighted_half_moment {P : ℝ} (hP : 25 ≤ P) :
    squareSum (totientRatioPower (1 / 2)) ⌊P⌋₊ ≤ 12.4 := by
  rw [squareSum_totientRatioPower]
  have hb : 25 ≤ ⌊P⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hP)
  have he : denominators P = Icc 1 25 ∪ Icc 26 ⌊P⌋₊ := by
    ext q
    simp only [denominators, mem_union, mem_Icc]
    omega
  have hd : Disjoint (Icc 1 (25 : ℕ)) (Icc 26 ⌊P⌋₊) := by
    apply disjoint_left.mpr
    intro q hq hq'
    have := mem_Icc.mp hq
    have := mem_Icc.mp hq'
    omega
  rw [he, sum_union hd]
  have ht := unweighted_tail_le (by norm_num : (1 / 2 : ℝ) < 1)
    (m := 26) (B := ⌊P⌋₊) (by norm_num)
  have hr : (26 : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 / 5 := by
    calc
      _ ≤ (25 : ℝ) ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
      _ = _ := by
        rw [show (25 : ℝ) = (5 : ℝ) ^ (2 : ℕ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
  norm_num only at ht hr
  linarith only [unweighted_small_head, ht, hr]

theorem source_inverse_sqrt {P : ℝ} (hP : 10000000000 ≤ P) :
    P ^ (-1 / 2 : ℝ) ≤ 0.00001 := by
  calc
    _ ≤ (10000000000 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hP (by norm_num)
    _ = _ := by
      rw [show (10000000000 : ℝ) = (10 : ℝ) ^ (10 : ℕ) by norm_num,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num

theorem unweighted_three_halves_normalized {P : ℝ} (hP : 10000000000 ≤ P) :
    squareSum (totientRatioPower (3 / 2)) ⌊P⌋₊ / P ≤ 0.000207 := by
  have hp : 0 < P := by linarith
  rw [squareSum_totientRatioPower]
  have h := unweighted_high_prefix_real (by norm_num : (1 : ℝ) < 3 / 2)
    (by norm_num) (show 1 ≤ P by linarith)
  have he : P ^ (1 / 2 : ℝ) / P = P ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hp, Real.rpow_one]
  have hd := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10000000000) hP
  norm_num only at h
  calc
    _ ≤ (10.3 * (1 + P ^ (1 / 2 : ℝ) / (1 / 2))) / P :=
      div_le_div_of_nonneg_right (by convert! h using 1; norm_num) hp.le
    _ = 10.3 * (1 / P) + 20.6 * P ^ (-1 / 2 : ℝ) := by rw [← he]; ring
    _ ≤ 10.3 * (1 / 10000000000) + 20.6 * 0.00001 :=
      add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num))
        (mul_le_mul_of_nonneg_left (source_inverse_sqrt hP) (by norm_num))
    _ ≤ _ := by norm_num

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart
