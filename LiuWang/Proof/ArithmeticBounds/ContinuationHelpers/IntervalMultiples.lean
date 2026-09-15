import LiuWang.Proof.ArithmeticBounds.ContinuationHelpers.SquarefreeSieve
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear
import Mathlib.Algebra.Order.Floor.Semifield

/-! 实端点区间内倍数计数的双侧误差；左开右闭端点不作平移。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.ContinuationHelpers

open scoped BigOperators

theorem sum_dvdIndicator_Ioc (a b d : Nat) (hab : a ≤ b) (hd : 0 < d) :
    (∑ n ∈ Finset.Ioc a b, dvdIndicator d n) =
      ((b / d : Nat) : Real) - ((a / d : Nat) : Real) := by
  have hIoc (R : Nat) : Finset.Ioc 0 R = Finset.Icc 1 R := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have h := Finset.sum_Ioc_consecutive (fun n => dvdIndicator d n) (Nat.zero_le a) hab
  rw [hIoc, hIoc] at h
  simp only [dvdIndicator,
    AnalyticNumberTheory.LargeSieve.sum_dvd_indicator_Icc _ _ hd] at h
  dsimp [dvdIndicator]
  linarith

theorem dyadic_dvdIndicator_bounds {M : Real} (hM : 0 ≤ M) (d : Nat) (hd : 0 < d) :
    M / d - 1 ≤ ∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, dvdIndicator d n ∧
    (∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, dvdIndicator d n) ≤ M / d + 1 := by
  rw [sum_dvdIndicator_Ioc _ _ _ (Nat.floor_mono (by linarith)) hd]
  rw [← Nat.floor_div_natCast, ← Nat.floor_div_natCast]
  have hlow := Nat.floor_le (show (0 : Real) ≤ M / d by positivity)
  have hhigh := Nat.floor_le (show (0 : Real) ≤ 2 * M / d by positivity)
  have hlow' := Nat.lt_floor_add_one (M / d)
  have hhigh' := Nat.lt_floor_add_one (2 * M / d)
  have he : 2 * M / d = 2 * (M / d) := by ring
  rw [he] at hhigh hhigh' ⊢
  constructor <;> linarith

theorem dyadic_oddSquareIndicator_bounds {M : Real} (hM : 0 ≤ M)
    (d : Nat) (hd : 0 < d) :
    M * oddDensity d - 2 ≤
      ∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, oddSquareIndicator d n ∧
    (∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, oddSquareIndicator d n) ≤
      M * oddDensity d + 2 := by
  have h := dyadic_dvdIndicator_bounds hM d hd
  have h' := dyadic_dvdIndicator_bounds hM (Nat.lcm 4 d) (Nat.lcm_pos (by norm_num) hd)
  simp only [oddSquareIndicator, Finset.sum_sub_distrib, oddDensity]
  simp only [div_eq_mul_inv] at h h' ⊢
  constructor <;> nlinarith [h.1, h.2, h'.1, h'.2]

end LiuWang.Proof.ArithmeticBounds.ContinuationHelpers
