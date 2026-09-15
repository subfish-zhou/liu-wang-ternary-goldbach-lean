import LiuWang.Proof.DirichletZeroCount.Applications.Coarse

/-!
# The literal Theorem 7 bound, paid unconditionally on the low-alpha branch

The left side is the frozen full-family ordinary-L analytic-multiplicity count.
No zero-density, mean-value, or sharp argument-variation estimate is an input.
-/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.DirichletZeroCount.Applications

def sourceSevenBound (q : ℕ) (alpha y : ℝ) : ℝ :=
  16541 * (Real.log y) ^ (6 : ℕ) +
    (17102 + 254231 / Real.log ((q : ℝ) * y)) *
      ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
      (Real.log ((q : ℝ) * y)) ^ (6 * alpha)

theorem density_power_ge_product {q y alpha : ℝ} (hq : 1 ≤ q) (hy : 1 ≤ y)
    (halpha : alpha ≤ 2 / 3) :
    q * y ≤ (q ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) := by
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul (by linarith : 0 ≤ q),
    ← Real.rpow_natCast_mul (by linarith : 0 ≤ y)]
  have hqpow : q ≤ q ^ ((3 : ℝ) * (1 - alpha)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq (by linarith : (1 : ℝ) ≤ 3 * (1 - alpha))
  have hypow : y ≤ y ^ ((4 : ℝ) * (1 - alpha)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hy (by linarith : (1 : ℝ) ≤ 4 * (1 - alpha))
  exact mul_le_mul hqpow hypow (by linarith) (by positivity)

theorem sourceSevenBound_ge_ten {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hy : 10000 ≤ y) (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 2 / 3) :
    10 * q * y * Real.log ((q : ℝ) * y) ≤ sourceSevenBound q alpha y := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hS := log_product_ge_eight hq hy
  have hpow := density_power_ge_product hq (by linarith : 1 ≤ y) halpha'
  have hlogpow : Real.log ((q : ℝ) * y) ≤
      (Real.log ((q : ℝ) * y)) ^ (6 * alpha) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ Real.log ((q : ℝ) * y)) (by linarith : (1 : ℝ) ≤ 6 * alpha)
  have hcoeff : (10 : ℝ) ≤ 17102 + 254231 / Real.log ((q : ℝ) * y) := by
    have h : 0 ≤ 254231 / Real.log ((q : ℝ) * y) := by positivity
    linarith
  have hmain :
      (q : ℝ) * y * Real.log ((q : ℝ) * y) ≤
        ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
          (Real.log ((q : ℝ) * y)) ^ (6 * alpha) :=
    mul_le_mul hpow hlogpow (by linarith) (by positivity)
  have h := mul_le_mul hcoeff hmain (by positivity) (by positivity)
  have hfirst : 0 ≤ 16541 * (Real.log y) ^ (6 : ℕ) := by positivity
  unfold sourceSevenBound
  nlinarith only [h, hfirst]

theorem familyCount_le_sourceSeven_low (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : 10000 ≤ y) (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 2 / 3) :
    (familyCount q alpha y : ℝ) ≤
      16541 * (Real.log y) ^ (6 : ℕ) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
          (Real.log ((q : ℝ) * y)) ^ (6 * alpha) :=
  (familyCount_le_ten q alpha hy).trans (sourceSevenBound_ge_ten hy halpha halpha')

theorem source_height_ge_ten_thousand {q : ℕ} [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) : 10000 ≤ y := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hdiv := (max_le_iff.mp hy).1
  have hy0 : 0 < y := (div_pos (by norm_num) hq).trans_le hdiv
  by_cases hsmall : q ≤ 10
  · have hq10 : (q : ℝ) ≤ 10 := Nat.cast_le.mpr hsmall
    have h := (div_le_iff₀ hq).mp hdiv
    nlinarith
  · have hq10 : (10 : ℝ) ≤ q := Nat.cast_le.mpr (le_of_lt (Nat.lt_of_not_ge hsmall))
    have hlog : 1 ≤ Real.log q :=
      (Real.le_log_iff_exp_le hq).mpr (Real.exp_one_lt_three.le.trans (by linarith))
    linarith [(max_le_iff.mp hy).2]

def sourceDelta (y : ℝ) : ℝ := 1 / (1.5 * Real.log y)

theorem sourceDelta_le_twelfth {y : ℝ} (hy : 10000 ≤ y) :
    sourceDelta y ≤ 1 / 12 := by
  have hlog := log_height_ge_eight hy
  unfold sourceDelta
  exact (div_le_iff₀ (by linarith : 0 < 1.5 * Real.log y)).mpr (by linarith)

theorem familyCount_le_sourceSeven_original_low (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 1 / 2 + 2 * sourceDelta y) :
    (familyCount q alpha y : ℝ) ≤
      16541 * (Real.log y) ^ (6 : ℕ) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
          (Real.log ((q : ℝ) * y)) ^ (6 * alpha) := by
  have hy' := source_height_ge_ten_thousand hy
  exact familyCount_le_sourceSeven_low q hy' halpha
    (by linarith [sourceDelta_le_twelfth hy'])

end LiuWang.Proof.DirichletZeroCount.Applications
