import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.Effective.Scale

/-! Explicit rounding, harmonic, mollifier and PV costs for the fixed balancing truncation. -/

set_option autoImplicit false
noncomputable section

open Finset
open MathlibNt.SieveTheory.LiuWeight
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective

theorem rounded_powers (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    y * (⌈(q : ℝ) * y⌉₊ : ℝ) ^ (1 - 2 * sigma) ≤ balancedPower q y sigma ∧
    (balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊ : ℕ) ^ (2 - 2 * sigma) / (q : ℝ) ≤
      4 * balancedPower q y sigma ∧
    (q : ℝ) * y ^ 3 * (balancedLength q y sigma : ℝ) ^ (-2 * sigma) ≤ balancedPower q y sigma := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hy0 : 0 < y := by linarith
  have hp := ceil_parameters q hy
  have hm := balancedLength_bounds q hy hqy hs
  have hT := truncationScale_pos hq0 hy0 sigma
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (mul_pos hq0 hy0) hp.2.2.1 (by linarith [hs.1])) hy0.le).trans
      (balanced_diagonal_le hq (by linarith) hs)
  · have hMN : ((balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊ : ℕ) : ℝ) ≤
        4 * (truncationScale q y sigma * ((q : ℝ) * y)) := by
      have h := mul_le_mul hm.2.2.2 hp.2.2.2 (Nat.cast_nonneg _) (by positivity)
      push_cast
      nlinarith only [h]
    have he : 0 ≤ 2 - 2 * sigma := by linarith [hs.2]
    have hc : (4 : ℝ) ^ (2 - 2 * sigma) ≤ 4 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 4) (show 2 - 2 * sigma ≤ 1 by linarith [hs.1])
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊)) hMN he
    rw [Real.mul_rpow (by norm_num) (mul_pos hT (mul_pos hq0 hy0)).le] at hpow
    have hb := hpow.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by positivity) _))
    have hd := div_le_div_of_nonneg_right hb hq0.le
    have hid := balanced_offDiagonal_identity hq0 hy0 sigma
    calc
      _ ≤ (4 * (truncationScale q y sigma * ((q : ℝ) * y)) ^ (2 - 2 * sigma)) / q := hd
      _ = 4 * balancedPower q y sigma := by rw [mul_div_assoc, hid]
  · have h := Real.rpow_le_rpow_of_nonpos hT hm.2.2.1 (show -2 * sigma ≤ 0 by linarith [hs.1])
    exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (q : ℝ) * y ^ 3)).trans_eq
      (balanced_tail_identity hq0 hy0 sigma)

theorem balanced_harmonics (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    liuHarmonic (balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊) ≤
      4 * (1 + Real.log ((q : ℝ) * y)) ∧
    harmonicRange ((balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊ + 1) / q + 1) ≤
      5 * (1 + Real.log ((q : ℝ) * y)) := by
  have hp := ceil_parameters q hy
  have hm := (balancedLength_bounds q hy hqy hs).2.1
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hh := right_harmonics q ⌈(q : ℝ) * y⌉₊ (by nlinarith) hp.1 hp.2.2.2
  have hprod := Nat.mul_le_mul_right ⌈(q : ℝ) * y⌉₊ hm
  constructor
  · apply le_trans _ hh.1
    unfold liuHarmonic
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hprod) (fun _ _ _ => by positivity)
  · apply le_trans _ hh.2.1
    unfold harmonicRange
    exact sum_le_sum_of_subset_of_nonneg
      (range_mono (Nat.add_le_add_right (Nat.div_le_div_right (Nat.add_le_add_right hprod 1)) 1))
      (fun _ _ _ => by positivity)

theorem prefixBudget_sq_le_log (q : ℕ) [NeZero q] {y : ℝ} (hy : 2 ≤ y) :
    prefixBudget q ^ 2 ≤ 64 * q * (1 + Real.log ((q : ℝ) * y)) ^ 2 := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hlq := Real.log_nonneg hq
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < q)
    (show (q : ℝ) ≤ (q : ℝ) * y by nlinarith)
  have h := pow_le_pow_left₀ (prefixBudget_nonneg q)
    (min_le_right (q : ℝ) (8 * Real.sqrt q * (1 + Real.log q))) 2
  have h1 : prefixBudget q ^ 2 ≤ 64 * q * (1 + Real.log q) ^ 2 := by
    apply h.trans_eq
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
    ring
  exact h1.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log q) (by linarith) 2)
    (by positivity : 0 ≤ 64 * (q : ℝ)))

theorem balanced_finite_cost (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    (4 * y * (⌈(q : ℝ) * y⌉₊ : ℝ) ^ (1 - 2 * sigma) +
      12 / (q : ℝ) * harmonicRange ((balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊ + 1) / q + 1) *
        (balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊ : ℕ) ^ (2 - 2 * sigma)) *
      liuHarmonic (balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊) ^ 4 ≤
        62464 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  let L := 1 + Real.log ((q : ℝ) * y)
  let W := balancedPower q y sigma
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hL : 1 ≤ L := by dsimp [L]; have := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by nlinarith); linarith
  have hW : 0 ≤ W := (balancedPower_pos (by positivity) (by linarith) sigma).le
  have hp := rounded_powers q hy hqy hs
  have hh := balanced_harmonics q hy hqy hs
  have hd := mul_le_mul_of_nonneg_left hp.1 (by norm_num : (0 : ℝ) ≤ 4)
  have ho := mul_le_mul hp.2.1 hh.2 (harmonicRange_nonneg _)
    (show 0 ≤ 4 * W by positivity)
  have hWL : W ≤ W * L := le_mul_of_one_le_right hW hL
  have hsum : 4 * y * (⌈(q : ℝ) * y⌉₊ : ℝ) ^ (1 - 2 * sigma) +
      12 / (q : ℝ) * harmonicRange ((balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊ + 1) / q + 1) *
        (balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊ : ℕ) ^ (2 - 2 * sigma) ≤ 244 * W * L := by
    dsimp [W, L] at hWL ⊢
    simp only [div_eq_mul_inv] at ho ⊢
    nlinarith only [hd, ho, hWL]
  have hH := pow_le_pow_left₀
    (show 0 ≤ liuHarmonic (balancedLength q y sigma * ⌈(q : ℝ) * y⌉₊) by unfold liuHarmonic; positivity)
    hh.1 4
  have h := mul_le_mul hsum hH (by positivity) (show 0 ≤ 244 * W * L by positivity)
  exact h.trans_eq (by dsimp [W, L]; ring)

theorem balanced_remainder_cost (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    2 * pvError q (balancedLength q y sigma) sigma y ^ 2 * mollifierMeanBound q ((q : ℝ) * y) y ≤
      106496 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  let L := 1 + Real.log ((q : ℝ) * y)
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hL : 1 ≤ L := by dsimp [L]; have := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by nlinarith); linarith
  have hW := (balancedPower_pos (show (0 : ℝ) < q by positivity) (by linarith : 0 < y) sigma).le
  have hab : (1 + y) ^ 2 ≤ 4 * y ^ 2 := by nlinarith
  have hpre := mul_le_mul (prefixBudget_sq_le_log q hy) hab (sq_nonneg _)
    (by positivity : 0 ≤ 64 * (q : ℝ) * L ^ 2)
  have hpre' := mul_le_mul_of_nonneg_right hpre
    (Real.rpow_nonneg (Nat.cast_nonneg (balancedLength q y sigma)) (-2 * sigma))
  have hQ := mul_le_mul hpre' (right_mollifier_cost q hy)
    (mollifierMeanBound_nonneg q _ (by linarith)) (by positivity)
  have hpow := mul_le_mul_of_nonneg_right (rounded_powers q hy hqy hs).2.2
    (by positivity : 0 ≤ 106496 * L ^ 4)
  have hlast := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : 4 ≤ 5))
    (show 0 ≤ 106496 * balancedPower q y sigma by positivity)
  rw [pvError_sq]
  dsimp [L] at hpow hlast ⊢
  nlinarith only [hQ, hpow, hlast]

theorem balanced_budget_bound (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    pvBudget q ((q : ℝ) * y) (balancedLength q y sigma) sigma y ≤
      168960 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  exact (add_le_add (balanced_finite_cost q hy hqy hs) (balanced_remainder_cost q hy hqy hs)).trans_eq
    (by ring)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective
