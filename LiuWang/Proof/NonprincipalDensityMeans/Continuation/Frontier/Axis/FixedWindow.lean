import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.WindowScale

/-! Actual endpoint windows for one fixed X = q y and all half-heights u. -/

set_option autoImplicit false
noncomputable section

open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

def rightBudget (q : ℕ) (y : ℝ) : ℝ :=
  18048 * (1 + Real.log ((q : ℝ) * y)) ^ 5 / q

def criticalBudget (q : ℕ) (X : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  2 * meanFactor q (M * ⌈X⌉₊ + 1) y * liuHarmonic (M * ⌈X⌉₊) ^ 4 +
    8 * prefixBudget q ^ 2 * (1 + y) ^ 2 / M * mollifierMeanBound q X y

theorem rightBudget_nonneg (q : ℕ) [NeZero q] {y : ℝ} (hy : 2 ≤ y) :
    0 ≤ rightBudget q y := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hl := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by nlinarith)
  unfold rightBudget
  positivity

theorem criticalBudget_nonneg (q : ℕ) (X : ℝ) (M : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ criticalBudget q X M y :=
  add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (meanFactor_nonneg q _ hy)) (by positivity))
    (mul_nonneg (by positivity) (mollifierMeanBound_nonneg q X hy))

theorem right_mother_at_scale (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : 1 ≤ sigma) :
    (4 * y / ⌈(q : ℝ) * y⌉₊ +
      12 / (q : ℝ) * harmonicRange ((⌈(q : ℝ) * y⌉₊ ^ 2 * ⌈(q : ℝ) * y⌉₊ + 1) / q + 1)) *
        liuHarmonic (⌈(q : ℝ) * y⌉₊ ^ 2 * ⌈(q : ℝ) * y⌉₊) ^ 4 +
      2 * stripError q (⌈(q : ℝ) * y⌉₊ ^ 2) sigma y ^ 2 *
        mollifierMeanBound q ((q : ℝ) * y) y ≤ rightBudget q y := by
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hz : 2 ≤ (q : ℝ) * y := by nlinarith
  have hL : 1 ≤ 1 + Real.log ((q : ℝ) * y) := (right_log_N hz hp.1 hp.2.2.2).1
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left (right_error_cost q hy hs) (by norm_num : (0 : ℝ) ≤ 2))
    (right_mollifier_cost q hy) (mollifierMeanBound_nonneg q _ (by linarith))
    (by positivity : 0 ≤ 2 * (16 / ((q : ℝ) * y)))
  have hre : 2 * stripError q (⌈(q : ℝ) * y⌉₊ ^ 2) sigma y ^ 2 *
      mollifierMeanBound q ((q : ℝ) * y) y ≤
      1664 * (1 + Real.log ((q : ℝ) * y)) ^ 2 / q := by
    apply hm.trans_eq
    field_simp
    ring
  have hlast := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by norm_num : 2 ≤ 5))
    (by positivity : 0 ≤ 1664 / (q : ℝ))
  have hf := right_finite_cost q hy
  unfold rightBudget
  simp only [div_eq_mul_inv] at hf hre hlast ⊢
  nlinarith only [hf, hre, hlast]

theorem Fmean_right_fixed_X (q : ℕ) [NeZero q] {y sigma u : ℝ}
    (hy : 2 ≤ y) (hs : 1 ≤ sigma) (hu : 0 ≤ u) :
    Fmean q ((q : ℝ) * y) sigma u ≤
      (1 + u / y) ^ 3 * rightBudget q y := by
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX : 1 < (q : ℝ) * y := by nlinarith
  have hNM := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) ⌈(q : ℝ) * y⌉₊
  exact (right_mother_height_le q ((q : ℝ) * y) hX hNM hp.2.1 hs
    (by linarith) hu).trans
    (mul_le_mul_of_nonneg_left (right_mother_at_scale q hy hs) (by positivity))

theorem Fmean_critical_fixed_X (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : 2 ≤ y) (hu : 0 ≤ u) {M : ℕ} (hM : 2 ≤ M) :
    Fmean q ((q : ℝ) * y) (1 / 2) u ≤
      (1 + u / y) ^ 3 * criticalBudget q ((q : ℝ) * y) M y := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  exact critical_mother_height_le q ((q : ℝ) * y) hM (by nlinarith) (by linarith) hu

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
