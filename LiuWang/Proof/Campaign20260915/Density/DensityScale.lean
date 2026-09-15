import LiuWang.Proof.Campaign20260915.Density.MovingVertical
import LiuWang.Proof.Campaign20260915.Density.MaximumPayment

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_shift_log (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    sourceDelta ((q : ℝ) * y) * Real.log ((q : ℝ) * y) = 2 / 3 := by
  have hL := source_product_log_ge_eleven q hy
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  unfold sourceDelta
  field_simp
  norm_num

theorem source_density_log_bounds (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    2 * Real.log ((q : ℝ) * y) + 6 * Real.log (Real.log ((q : ℝ) * y)) ≤
        Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ∧
      Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ≤ 4 * Real.log ((q : ℝ) * y) := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  have hy' : 10000 ≤ y := source_height_ge_ten_thousand hy
  have hy0 : 0 < y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX0 : 0 < X := by dsimp [X]; positivity
  have hL := source_product_log_ge_eleven q hy
  have hL0 : 0 < L := by dsimp [L, X]; linarith
  have hp := Real.pow_div_factorial_le_exp L hL0.le 6
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hp
  rw [Real.exp_log hX0] at hp
  have hm := mul_le_mul_of_nonneg_left hy' hX0.le
  have hprod : L ^ (6 : ℕ) ≤ X * y := by nlinarith only [hp, hm, hX0]
  have hlog := Real.log_le_log (pow_pos hL0 6) hprod
  rw [Real.log_pow, Real.log_mul hX0.ne' hy0.ne'] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have he : (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) = X ^ (3 : ℕ) * y := by dsimp [X]; ring
  have heL : Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) = 3 * L + Real.log y := by
    rw [he, Real.log_mul (by positivity) hy0.ne', Real.log_pow]
    rfl
  have hly : Real.log y ≤ L := Real.log_le_log hy0 (by dsimp [X]; nlinarith)
  change 2 * L + 6 * Real.log L ≤ _ ∧ _ ≤ 4 * L
  rw [heL]
  constructor <;> linarith

theorem source_density_scale_pos (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (alpha : ℝ) :
    0 < chenDensityScale q y alpha := by
  have hy0 : 0 < y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
  unfold chenDensityScale
  positivity

theorem source_density_scale_log (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (alpha : ℝ) :
    Real.log (chenDensityScale q y alpha) =
      (1 - alpha) * Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) +
        6 * alpha * Real.log (Real.log ((q : ℝ) * y)) := by
  have hy0 : 0 < y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
  unfold chenDensityScale
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow hL0]

theorem source_density_scale_antitone (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    Antitone (chenDensityScale q y) := by
  have h := (source_density_log_bounds q hy).1
  have hL := source_product_log_ge_eleven q hy
  intro a b hab
  have hm := mul_nonneg (sub_nonneg.mpr hab)
    (show 0 ≤ Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) -
      6 * Real.log (Real.log ((q : ℝ) * y)) by linarith)
  apply (Real.log_le_log_iff (source_density_scale_pos q hy b) (source_density_scale_pos q hy a)).mp
  rw [source_density_scale_log q hy b, source_density_scale_log q hy a]
  nlinarith only [hm]

theorem source_density_scale_ge_right (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (ha : alpha ≤ 1) :
    ((q : ℝ) * y) ^ (2 * (1 - alpha)) * Real.log ((q : ℝ) * y) ^ (6 : ℕ) ≤
      chenDensityScale q y alpha := by
  have hy0 : 0 < y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < (q : ℝ) * y := by positivity
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
  have hm := mul_le_mul_of_nonneg_left (source_density_log_bounds q hy).1
    (show 0 ≤ 1 - alpha by linarith)
  apply (Real.log_le_log_iff (by positivity) (source_density_scale_pos q hy alpha)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hX0, Real.log_pow,
    source_density_scale_log q hy alpha]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hm]

theorem source_density_scale_ge_log_six (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (ha : alpha ≤ 1) :
    Real.log ((q : ℝ) * y) ^ (6 : ℕ) ≤ chenDensityScale q y alpha := by
  have hy1 : 1 ≤ y := by linarith [source_height_ge_ten_thousand hy]
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hp := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hq hy1)
    (show 0 ≤ 2 * (1 - alpha) by linarith)
  exact (le_mul_of_one_le_left (by positivity) hp).trans (source_density_scale_ge_right q hy ha)

end LiuWang.Proof.Campaign20260915.Density
