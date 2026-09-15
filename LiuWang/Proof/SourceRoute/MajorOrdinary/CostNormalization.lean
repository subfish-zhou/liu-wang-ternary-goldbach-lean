import LiuWang.Proof.SourceRoute.MajorOrdinary.Interactions

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

theorem cube_rpow_one_third {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 3) ^ (1 / 3 : ℝ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem cube_rpow_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 3) ^ (2 / 3 : ℝ) = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem packetCubicBound_one_third {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    packetCubicBound N q ^ (1 / 3 : ℝ) =
      (2 * deltaRadius N q) ^ (1 / 3 : ℝ) * packetBound N q := by
  rw [packetCubicBound, Real.mul_rpow
    (by linarith [deltaRadius_pos hN (NeZero.pos q)])
    (pow_nonneg (packetBound_nonneg N q) 3),
    cube_rpow_one_third (packetBound_nonneg N q)]

theorem packetCubicBound_two_thirds {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    packetCubicBound N q ^ (2 / 3 : ℝ) =
      (2 * deltaRadius N q) ^ (2 / 3 : ℝ) * packetBound N q ^ 2 := by
  rw [packetCubicBound, Real.mul_rpow
    (by linarith [deltaRadius_pos hN (NeZero.pos q)])
    (pow_nonneg (packetBound_nonneg N q) 3),
    cube_rpow_two_thirds (packetBound_nonneg N q)]

theorem moebius_abs_sq (q : ℕ) :
    |(ArithmeticFunction.moebius q : ℝ)| ^ 2 = |(ArithmeticFunction.moebius q : ℝ)| := by
  rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> norm_num [h]

theorem linearCost_explicit {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    linearCost N q =
      3 * |(ArithmeticFunction.moebius q : ℝ)| * Real.sqrt (q : ℝ) /
        (q.totient : ℝ) ^ 2 *
      jCubicBound N ^ (2 / 3 : ℝ) * (2 * deltaRadius N q) ^ (1 / 3 : ℝ) *
        (N : ℝ) * (lowWeightSum N q + 5 * highWeightSum N q) := by
  have hp : (q.totient : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))).ne'
  rw [linearCost, dif_neg (NeZero.ne q), norm_principalCoefficient,
    principalMass, packetCubicBound_one_third hN, packetBound, zeroEnvelope_split,
    div_pow, moebius_abs_sq]
  field_simp

theorem quadraticCost_explicit {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    quadraticCost N q =
      3 * |(ArithmeticFunction.moebius q : ℝ)| * (q : ℝ) /
        (q.totient : ℝ) ^ 2 *
      jCubicBound N ^ (1 / 3 : ℝ) * (2 * deltaRadius N q) ^ (2 / 3 : ℝ) *
        (N : ℝ) ^ 2 * (lowWeightSum N q + 5 * highWeightSum N q) ^ 2 := by
  have hp : (q.totient : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))).ne'
  rw [quadraticCost, dif_neg (NeZero.ne q), norm_principalCoefficient,
    principalMass, packetCubicBound_two_thirds hN, packetBound, zeroEnvelope_split]
  simp only [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  field_simp

theorem cubicCost_explicit {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    cubicCost N q =
      (3.36 / (5 * Real.pi)) * Real.sqrt (q : ℝ) / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * sourceP N *
          (lowWeightSum N q + 5 * highWeightSum N q) ^ 3 := by
  have hn := natCast_pos_of_exp_le hN
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hp : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hs : Real.sqrt (q : ℝ) ^ 3 = (q : ℝ) * Real.sqrt (q : ℝ) := by
    rw [pow_succ, Real.sq_sqrt hq.le]
  rw [cubicCost, dif_neg (NeZero.ne q), packetCubicBound, packetBound,
    zeroEnvelope_split, deltaRadius]
  simp only [mul_pow, div_pow, hs]
  field_simp
  ring

theorem I12_explicit {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖I12 N‖ ≤ ∑ q ∈ denominators (sourceP N),
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        3 * |(ArithmeticFunction.moebius q : ℝ)| * Real.sqrt (q : ℝ) /
          (q.totient : ℝ) ^ 2 *
        jCubicBound N ^ (2 / 3 : ℝ) * (2 * deltaRadius N q) ^ (1 / 3 : ℝ) *
          (N : ℝ) * (lowWeightSum N q + 5 * highWeightSum N q) := by
  apply (I12_bound hN).trans_eq
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
  let : NeZero q := ⟨hq0⟩
  simpa only [dif_neg hq0] using linearCost_explicit (q := q) hN

end LiuWang.Proof.SourceRoute.MajorOrdinary
