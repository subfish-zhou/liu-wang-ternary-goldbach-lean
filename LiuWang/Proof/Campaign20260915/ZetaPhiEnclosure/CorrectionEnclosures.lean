import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.DerivativeApproximation

set_option autoImplicit false
noncomputable section

open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaValidation

def RationalBall.add (a b : RationalBall) : RationalBall :=
  ⟨a.center + b.center, a.radius + b.radius⟩

theorem RationalBall.add_correct {a b : RationalBall} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) : (a.add b).Contains (x + y) := by
  have h := abs_add_le (x - (a.center : ℝ)) (y - (b.center : ℝ))
  simp only [Contains, add, Rat.cast_add]
  rw [show x + y - ((a.center : ℝ) + b.center) =
    (x - a.center) + (y - b.center) by ring]
  exact h.trans (add_le_add ha hb)

def RationalBall.divide (b : RationalBall) (a ea lower : ℚ) : RationalBall :=
  let q := b.center / max (lower / 2) a
  ⟨q, (b.radius + |q| * ea) / lower⟩

theorem RationalBall.divide_correct {b : RationalBall} {x D : ℝ} {a ea lower : ℚ}
    (hb : b.Contains x) (hl : 0 < lower) (hD : (lower : ℝ) ≤ D)
    (ha : |D - (a : ℝ)| ≤ (ea : ℝ)) :
    (b.divide a ea lower).Contains (x / D) := by
  let S : ℝ := max ((lower : ℝ) / 2) a
  let q : ℝ := (b.center : ℝ) / S
  have hlR : (0 : ℝ) < lower := by exact_mod_cast hl
  have hS : 0 < S := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hDS : |D - S| ≤ (ea : ℝ) := clamp_error (by linarith) ha
  have hq : (b.center : ℝ) = q * S := (div_mul_cancel₀ _ hS.ne').symm
  have he : |x / D - q| ≤ ((b.radius : ℝ) + |q| * ea) / lower := by
    rw [show x / D - q = (x - q * D) / D by field_simp [(hlR.trans_le hD).ne'],
      abs_div, abs_of_pos (hlR.trans_le hD)]
    have h : |x - q * D| ≤ (b.radius : ℝ) + |q| * ea := by
      rw [show x - q * D = (x - q * S) + q * (S - D) by ring]
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_sub_comm S D, ← hq]
      exact add_le_add hb (mul_le_mul_of_nonneg_left hDS (abs_nonneg q))
    exact div_le_div₀ ((abs_nonneg _).trans h) h hlR hD
  simpa only [Contains, divide, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_abs,
    Rat.cast_max, Rat.cast_ofNat, q, S] using he

def piSquareError (p ep : ℚ) : ℚ := ep * (4 + |p|)
def piFourthError (p ep : ℚ) : ℚ := piSquareError p ep * (16 + p ^ 2)

theorem piSquareError_correct (p ep : ℚ) (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ)) :
    |Real.pi ^ 2 - ((p ^ 2 : ℚ) : ℝ)| ≤ (piSquareError p ep : ℝ) := by
  have hsum : |Real.pi + (p : ℝ)| ≤ 4 + |(p : ℝ)| := by
    have h := abs_add_le Real.pi (p : ℝ)
    rw [abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_lt_four]
  simp only [piSquareError, Rat.cast_mul, Rat.cast_add, Rat.cast_abs, Rat.cast_ofNat, Rat.cast_pow]
  rw [show Real.pi ^ 2 - (p : ℝ) ^ 2 = (Real.pi - p) * (Real.pi + p) by ring, abs_mul]
  exact mul_le_mul hp hsum (abs_nonneg _) ((abs_nonneg _).trans hp)

theorem piFourthError_correct (p ep : ℚ) (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ)) :
    |Real.pi ^ 4 - ((p ^ 4 : ℚ) : ℝ)| ≤ (piFourthError p ep : ℝ) := by
  have h2 := piSquareError_correct p ep hp
  have hsum : |Real.pi ^ 2 + (p : ℝ) ^ 2| ≤ 16 + (p : ℝ) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  simp only [Rat.cast_pow] at h2
  simp only [piFourthError, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_pow]
  rw [show Real.pi ^ 4 - (p : ℝ) ^ 4 =
    (Real.pi ^ 2 - (p : ℝ) ^ 2) * (Real.pi ^ 2 + (p : ℝ) ^ 2) by ring, abs_mul]
  exact mul_le_mul h2 hsum (abs_nonneg _) ((abs_nonneg _).trans h2)

def inwardStep (r h : ℚ) : ℚ := if 0 ≤ r then -h else h

theorem inwardStep_ne_zero (r h : ℚ) (hh : 0 < h) : inwardStep r h ≠ 0 := by
  unfold inwardStep
  split_ifs <;> linarith

theorem inwardStep_domain (r h : ℚ) (hr : |(r : ℝ)| ≤ 1) (hh : 0 < h) (h6 : 6 * h ≤ 1)
    {n : ℕ} (hn : n ≤ 6) (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
    |((r + j * inwardStep r h : ℚ) : ℝ)| ≤ 1 := by
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast hjn.trans hn
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have h6R : 6 * (h : ℝ) ≤ 1 := by exact_mod_cast h6
  have hr' := abs_le.mp hr
  unfold inwardStep
  split_ifs with hr0
  · have hr0R : (0 : ℝ) ≤ r := by exact_mod_cast hr0
    push_cast
    rw [abs_le]
    constructor <;> nlinarith
  · have hr0R : (r : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hr0)
    push_cast
    rw [abs_le]
    constructor <;> nlinarith

def phiOneApprox (N : ℕ) (p ep r h d : ℚ) : RationalBall :=
  (derivativeApprox 3 N p ep r (inwardStep r h) d).divide
    (12 * p ^ 2) (12 * piSquareError p ep) 108

def phiTwoApprox (N : ℕ) (p ep r h d : ℚ) : RationalBall :=
  ((derivativeApprox 2 N p ep r (inwardStep r h) d).divide
    (16 * p ^ 2) (16 * piSquareError p ep) 144).add
    ((derivativeApprox 6 N p ep r (inwardStep r h) d).divide
      (288 * p ^ 4) (288 * piFourthError p ep) 23328)

theorem phiOneApprox_correct (N : ℕ) (p ep r h d : ℚ) {z : ℝ}
    (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ)) (hr : |(r : ℝ)| ≤ 1)
    (hh : 0 < h) (h6 : 6 * h ≤ 1) (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (phiOneApprox N p ep r h d).Contains (rsPhiOne z) := by
  have hb := derivativeApprox_correct 3 N (by simp) p ep r (inwardStep r h) d
    (inwardStep_ne_zero r h hh) hp hr (inwardStep_domain r h hr hh h6 (by norm_num)) hz hd
  apply RationalBall.divide_correct hb (by norm_num) (by norm_num; nlinarith [pi_square_lower])
  have he := mul_le_mul_of_nonneg_left (piSquareError_correct p ep hp)
    (by norm_num : (0 : ℝ) ≤ 12)
  simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, ← mul_sub, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 12)] using he

theorem phiTwoApprox_correct (N : ℕ) (p ep r h d : ℚ) {z : ℝ}
    (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ)) (hr : |(r : ℝ)| ≤ 1)
    (hh : 0 < h) (h6 : 6 * h ≤ 1) (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (phiTwoApprox N p ep r h d).Contains (rsPhiTwo z) := by
  have h2 := derivativeApprox_correct 2 N (by simp) p ep r (inwardStep r h) d
    (inwardStep_ne_zero r h hh) hp hr (inwardStep_domain r h hr hh h6 (by norm_num)) hz hd
  have h6' := derivativeApprox_correct 6 N (by simp) p ep r (inwardStep r h) d
    (inwardStep_ne_zero r h hh) hp hr (inwardStep_domain r h hr hh h6 (by norm_num)) hz hd
  apply RationalBall.add_correct
  · apply RationalBall.divide_correct h2 (by norm_num) (by norm_num; nlinarith [pi_square_lower])
    have he := mul_le_mul_of_nonneg_left (piSquareError_correct p ep hp)
      (by norm_num : (0 : ℝ) ≤ 16)
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 16)] using he
  · apply RationalBall.divide_correct h6' (by norm_num) (by norm_num; nlinarith [pi_fourth_lower])
    have he := mul_le_mul_of_nonneg_left (piFourthError_correct p ep hp)
      (by norm_num : (0 : ℝ) ≤ 288)
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 288)] using he

def phiOneEnclosure (N : ℕ) (r h d : ℚ) : RationalBall := phiOneApprox N piApprox piError r h d
def phiTwoEnclosure (N : ℕ) (r h d : ℚ) : RationalBall := phiTwoApprox N piApprox piError r h d

theorem phiOneEnclosure_correct (N : ℕ) (r h d : ℚ) {z : ℝ}
    (hr : |(r : ℝ)| ≤ 1) (hh : 0 < h) (h6 : 6 * h ≤ 1)
    (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (phiOneEnclosure N r h d).Contains (rsPhiOne z) :=
  phiOneApprox_correct N piApprox piError r h d piApprox_correct hr hh h6 hz hd

theorem phiTwoEnclosure_correct (N : ℕ) (r h d : ℚ) {z : ℝ}
    (hr : |(r : ℝ)| ≤ 1) (hh : 0 < h) (h6 : 6 * h ≤ 1)
    (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (phiTwoEnclosure N r h d).Contains (rsPhiTwo z) :=
  phiTwoApprox_correct N piApprox piError r h d piApprox_correct hr hh h6 hz hd

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
