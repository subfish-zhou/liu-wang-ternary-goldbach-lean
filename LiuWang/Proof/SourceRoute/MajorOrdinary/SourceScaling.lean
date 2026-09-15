import LiuWang.Proof.SourceRoute.MajorOrdinary.CostNormalization

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

theorem jCubicBound_rpow (N : ℕ) (s : ℝ) :
    jCubicBound N ^ s = (2.994006 / Real.pi) ^ s * (N : ℝ) ^ (2 * s) := by
  rw [jCubicBound, Real.mul_rpow (by positivity) (sq_nonneg _),
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

theorem double_delta_rpow {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (s : ℝ) :
    (2 * deltaRadius N q) ^ s =
      (3.36 / (5 * Real.pi)) ^ s * sourceL N ^ (3 * s) /
        ((q : ℝ) ^ s * (N : ℝ) ^ s) := by
  have hn := natCast_pos_of_exp_le hN
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL := sourceL_pos hN
  have he : 2 * deltaRadius N q =
      (3.36 / (5 * Real.pi)) * sourceL N ^ 3 / ((q : ℝ) * (N : ℝ)) := by
    unfold deltaRadius sourceP
    field_simp
    ring
  rw [he, Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (pow_nonneg hL.le 3), Real.mul_rpow hq.le hn.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  norm_num

theorem linearCost_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    linearCost N q =
      3 * (3.36 / (5 * Real.pi)) ^ (1 / 3 : ℝ) *
        (2.994006 / Real.pi) ^ (2 / 3 : ℝ) * (N : ℝ) ^ 2 * sourceL N *
        (|(ArithmeticFunction.moebius q : ℝ)| * (q : ℝ) ^ (1 / 6 : ℝ) /
          (q.totient : ℝ) ^ 2) *
        (lowWeightSum N q + 5 * highWeightSum N q) := by
  have hn := natCast_pos_of_exp_le hN
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hqroot : (q : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  have hnroot : (N : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  have hs : Real.sqrt (q : ℝ) =
      (q : ℝ) ^ (1 / 3 : ℝ) * (q : ℝ) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hq]
    norm_num
    exact Real.sqrt_eq_rpow _
  have hn43 : (N : ℝ) ^ (4 / 3 : ℝ) = (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) := by
    calc
      _ = (N : ℝ) ^ ((1 / 3 : ℝ) + 1) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]
  rw [linearCost_explicit hN, jCubicBound_rpow, double_delta_rpow hN]
  norm_num only [show (2 * (2 / 3) : ℝ) = 4 / 3 by norm_num,
    show (3 * (1 / 3) : ℝ) = 1 by norm_num, Real.rpow_one]
  rw [hs, hn43]
  field_simp

theorem quadraticCost_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    quadraticCost N q =
      3 * (3.36 / (5 * Real.pi)) ^ (2 / 3 : ℝ) *
        (2.994006 / Real.pi) ^ (1 / 3 : ℝ) * (N : ℝ) ^ 2 * sourceL N ^ 2 *
        (|(ArithmeticFunction.moebius q : ℝ)| * (q : ℝ) ^ (1 / 3 : ℝ) /
          (q.totient : ℝ) ^ 2) *
        (lowWeightSum N q + 5 * highWeightSum N q) ^ 2 := by
  have hn := natCast_pos_of_exp_le hN
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hqroot : (q : ℝ) ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  have hnroot : (N : ℝ) ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  have hs : (q : ℝ) =
      (q : ℝ) ^ (2 / 3 : ℝ) * (q : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hq]
    norm_num
  rw [quadraticCost_explicit hN, jCubicBound_rpow, double_delta_rpow hN]
  norm_num only [show (2 * (1 / 3) : ℝ) = 2 / 3 by norm_num,
    show (3 * (2 / 3) : ℝ) = 2 by norm_num, Real.rpow_ofNat]
  field_simp
  conv_lhs => rw [hs]
  ring

theorem cubicCost_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    cubicCost N q =
      (3.36 / (5 * Real.pi)) * (N : ℝ) ^ 2 * sourceL N ^ 3 *
        (Real.sqrt (q : ℝ) / (q.totient : ℝ) ^ 2) *
        (lowWeightSum N q + 5 * highWeightSum N q) ^ 3 := by
  rw [cubicCost_explicit hN, sourceP]
  ring

end LiuWang.Proof.SourceRoute.MajorOrdinary
