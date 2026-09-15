import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.LogBoundary

/-! The fixed balancing truncation, including real-power identities and rounding contracts. -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective

def truncationScale (q y sigma : ℝ) : ℝ := q ^ sigma * y ^ (sigma + 1 / 2)

def balancedPower (q y sigma : ℝ) : ℝ :=
  q ^ (1 - 2 * sigma ^ 2) * y ^ ((1 - sigma) * (2 * sigma + 3))

def balancedLength (q : ℕ) (y sigma : ℝ) : ℕ := ⌈truncationScale q y sigma⌉₊

theorem monomial_exp {q y : ℝ} (hq : 0 < q) (hy : 0 < y) (a b : ℝ) :
    q ^ a * y ^ b = Real.exp (Real.log q * a + Real.log y * b) := by
  rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hy, Real.exp_add]

theorem truncationScale_pos {q y : ℝ} (hq : 0 < q) (hy : 0 < y) (sigma : ℝ) :
    0 < truncationScale q y sigma :=
  mul_pos (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hy _)

theorem balancedPower_pos {q y : ℝ} (hq : 0 < q) (hy : 0 < y) (sigma : ℝ) :
    0 < balancedPower q y sigma :=
  mul_pos (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hy _)

theorem truncationScale_log {q y : ℝ} (hq : 0 < q) (hy : 0 < y) (sigma : ℝ) :
    Real.log (truncationScale q y sigma) =
      Real.log q * sigma + Real.log y * (sigma + 1 / 2) := by
  rw [truncationScale, monomial_exp hq hy, Real.log_exp]

theorem truncationScale_bounds {q y sigma : ℝ} (hq : 1 ≤ q) (hy : 2 ≤ y)
    (hqy : q ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    q * y ≤ truncationScale q y sigma ∧ truncationScale q y sigma ≤ (q * y) ^ (2 : ℕ) := by
  have hq0 : 0 < q := by linarith
  have hy0 : 0 < y := by linarith
  have hlq := Real.log_nonneg hq
  have hly := Real.log_nonneg (show 1 ≤ y by linarith)
  have hlqy := Real.log_le_log hq0 hqy
  have hprod : q * y = Real.exp (Real.log q + Real.log y) := by
    rw [Real.exp_add, Real.exp_log hq0, Real.exp_log hy0]
  constructor
  · rw [hprod, truncationScale, monomial_exp hq0 hy0, Real.exp_le_exp]
    have h1 := mul_nonneg (show 0 ≤ 1 - sigma by linarith [hs.2])
      (sub_nonneg.mpr hlqy)
    have h2 := mul_nonneg (show 0 ≤ 2 * sigma - 3 / 2 by linarith [hs.1]) hly
    nlinarith only [h1, h2]
  · have h1 := Real.rpow_le_rpow_of_exponent_le hq (show sigma ≤ 2 by linarith [hs.2])
    have h2 := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ y by linarith)
      (show sigma + 1 / 2 ≤ 2 by linarith [hs.2])
    have h : q ^ sigma * y ^ (sigma + 1 / 2) ≤ q ^ (2 : ℝ) * y ^ (2 : ℝ) :=
      mul_le_mul h1 h2 (Real.rpow_nonneg hy0.le _) (Real.rpow_nonneg hq0.le _)
    simpa only [truncationScale, Real.rpow_two, mul_pow] using h

theorem balancedLength_bounds (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    ⌈(q : ℝ) * y⌉₊ ≤ balancedLength q y sigma ∧
      balancedLength q y sigma ≤ ⌈(q : ℝ) * y⌉₊ ^ 2 ∧
      truncationScale q y sigma ≤ (balancedLength q y sigma : ℝ) ∧
      (balancedLength q y sigma : ℝ) ≤ 2 * truncationScale q y sigma := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have h := truncationScale_bounds hq hy hqy hs
  have hp := ceil_parameters q hy
  have ht : 2 ≤ truncationScale q y sigma := by
    have hz : 2 ≤ (q : ℝ) * y := by nlinarith
    exact hz.trans h.1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ truncationScale q y sigma by linarith)
  refine ⟨Nat.ceil_mono h.1, Nat.ceil_le.mpr ?_, Nat.le_ceil _, ?_⟩
  · exact h.2.trans (by
      simpa only [Nat.cast_pow] using pow_le_pow_left₀ (by positivity) hp.2.2.1 2)
  · change (⌈truncationScale q y sigma⌉₊ : ℝ) ≤ _
    linarith

theorem balanced_offDiagonal_identity {q y : ℝ} (hq : 0 < q) (hy : 0 < y) (sigma : ℝ) :
    (truncationScale q y sigma * (q * y)) ^ (2 - 2 * sigma) / q =
      balancedPower q y sigma := by
  rw [Real.rpow_def_of_pos (mul_pos (truncationScale_pos hq hy sigma) (mul_pos hq hy)),
    Real.log_mul (truncationScale_pos hq hy sigma).ne' (mul_pos hq hy).ne',
    truncationScale_log hq hy, Real.log_mul hq.ne' hy.ne']
  rw [show Real.exp ((Real.log q * sigma + Real.log y * (sigma + 1 / 2) +
      (Real.log q + Real.log y)) * (2 - 2 * sigma)) / q =
      Real.exp (((Real.log q * sigma + Real.log y * (sigma + 1 / 2) +
        (Real.log q + Real.log y)) * (2 - 2 * sigma)) - Real.log q) by
    rw [Real.exp_sub, Real.exp_log hq]]
  rw [balancedPower, monomial_exp hq hy]
  congr 1
  ring

theorem balanced_tail_identity {q y : ℝ} (hq : 0 < q) (hy : 0 < y) (sigma : ℝ) :
    q * y ^ (3 : ℕ) * truncationScale q y sigma ^ (-2 * sigma) =
      balancedPower q y sigma := by
  have hprod : q * y ^ (3 : ℕ) = Real.exp (Real.log q + 3 * Real.log y) := by
    rw [Real.exp_add, Real.exp_log hq,
      show 3 * Real.log y = Real.log y + Real.log y + Real.log y by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hy]
    ring
  rw [hprod, Real.rpow_def_of_pos (truncationScale_pos hq hy sigma),
    truncationScale_log hq hy, ← Real.exp_add, balancedPower, monomial_exp hq hy]
  congr 1
  ring

theorem balanced_diagonal_le {q y sigma : ℝ} (hq : 1 ≤ q) (hy : 1 ≤ y)
    (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    y * (q * y) ^ (1 - 2 * sigma) ≤ balancedPower q y sigma := by
  have hq0 : 0 < q := by linarith
  have hy0 : 0 < y := by linarith
  have he : y * (q * y) ^ (1 - 2 * sigma) =
      q ^ (1 - 2 * sigma) * y ^ (2 - 2 * sigma) := by
    rw [Real.mul_rpow hq0.le hy0.le,
      show 2 - 2 * sigma = 1 + (1 - 2 * sigma) by ring,
      Real.rpow_add hy0, Real.rpow_one]
    ring
  rw [he]
  have h1 := Real.rpow_le_rpow_of_exponent_le hq
    (show 1 - 2 * sigma ≤ 1 - 2 * sigma ^ 2 by
      nlinarith [mul_nonneg (show 0 ≤ sigma by linarith [hs.1]) (show 0 ≤ 1 - sigma by linarith [hs.2])])
  have h2 := Real.rpow_le_rpow_of_exponent_le hy
    (show 2 - 2 * sigma ≤ (1 - sigma) * (2 * sigma + 3) by
      nlinarith [mul_nonneg (show 0 ≤ 1 - sigma by linarith [hs.2])
        (show 0 ≤ 2 * sigma + 1 by linarith [hs.1])])
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hy0.le _) (Real.rpow_nonneg hq0.le _)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective
