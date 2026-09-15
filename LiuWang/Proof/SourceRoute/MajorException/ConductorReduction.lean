import LiuWang.Proof.SourceRoute.MajorException.PureTerms

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical Finset
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException

theorem moebiusWeight_eq (q : ℕ) :
    moebiusWeight q = if Squarefree q then 1 else 0 := by
  unfold moebiusWeight
  rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
  split_ifs <;> norm_num

theorem moebiusWeight_mul_le (d k : ℕ) :
    moebiusWeight (d*k) ≤ moebiusWeight d * moebiusWeight k := by
  by_cases h : Squarefree (d*k)
  · have hd : Squarefree d := fun x hx => h x (hx.trans (dvd_mul_right d k))
    have hk : Squarefree k := fun x hx => h x (hx.trans (dvd_mul_left k d))
    rw [moebiusWeight_eq, if_pos h, moebiusWeight_eq, if_pos hd,
      moebiusWeight_eq, if_pos hk]
    norm_num
  · rw [moebiusWeight_eq, if_neg h]
    exact mul_nonneg (moebiusWeight_nonneg d) (moebiusWeight_nonneg k)

def squarefreeTotientMass (X : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 X, moebiusWeight k/(k.totient : ℝ)^2

def totientMass (X : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 X, 1/(k.totient : ℝ)^2

theorem reciprocal_totient_product {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    1/((d*k).totient : ℝ)^2 ≤
      (1/(d.totient : ℝ)^2) * (1/(k.totient : ℝ)^2) := by
  have hdphi : 0 < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  have hkphi : 0 < (k.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hk)
  have hmul : (d.totient : ℝ)*(k.totient : ℝ) ≤ ((d*k).totient : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative d k
  have h := one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos hdphi hkphi))
    (pow_le_pow_left₀ (mul_nonneg hdphi.le hkphi.le) hmul 2)
  simpa only [mul_pow, one_div, mul_inv] using h

theorem squarefree_totient_multiples (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Icc 1 X, if d ∣ q then moebiusWeight q/(q.totient : ℝ)^2 else 0) ≤
      (moebiusWeight d/(d.totient : ℝ)^2) * squarefreeTotientMass (X/d) := by
  rw [Uniform.sum_multiples _ X hd, squarefreeTotientMass, mul_sum]
  apply sum_le_sum
  intro k hk
  have h := mul_le_mul (moebiusWeight_mul_le d k)
    (reciprocal_totient_product hd (mem_Icc.mp hk).1) (by positivity)
    (mul_nonneg (moebiusWeight_nonneg d) (moebiusWeight_nonneg k))
  simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem totient_multiples (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Icc 1 X, if d ∣ q then 1/(q.totient : ℝ)^2 else 0) ≤
      (1/(d.totient : ℝ)^2) * totientMass (X/d) := by
  rw [Uniform.sum_multiples _ X hd, totientMass, mul_sum]
  exact sum_le_sum (fun k hk => reciprocal_totient_product hd (mem_Icc.mp hk).1)

theorem source_linear_conductor_reduction (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Icc 1 X,
      if d ∣ q then moebiusWeight q*Real.sqrt d/(q.totient : ℝ)^2 else 0) ≤
      (moebiusWeight d*Real.sqrt d/(d.totient : ℝ)^2) *
        squarefreeTotientMass (X/d) := by
  have h := mul_le_mul_of_nonneg_left (squarefree_totient_multiples X hd)
    (Real.sqrt_nonneg (d : ℝ))
  rw [mul_sum] at h
  have he (q : ℕ) : Real.sqrt d *
      (if d ∣ q then moebiusWeight q/(q.totient : ℝ)^2 else 0) =
      (if d ∣ q then moebiusWeight q*Real.sqrt d/(q.totient : ℝ)^2 else 0) := by
    split_ifs <;> ring
  simp only [he] at h
  exact h.trans_eq (by ring)

theorem source_quadratic_conductor_reduction (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Icc 1 X,
      if d ∣ q then moebiusWeight q*(d : ℝ)/(q.totient : ℝ)^2 else 0) ≤
      (moebiusWeight d*(d : ℝ)/(d.totient : ℝ)^2) *
        squarefreeTotientMass (X/d) := by
  have h := mul_le_mul_of_nonneg_left (squarefree_totient_multiples X hd)
    (Nat.cast_nonneg (α := ℝ) d)
  rw [mul_sum] at h
  have he (q : ℕ) : (d : ℝ) *
      (if d ∣ q then moebiusWeight q/(q.totient : ℝ)^2 else 0) =
      (if d ∣ q then moebiusWeight q*(d : ℝ)/(q.totient : ℝ)^2 else 0) := by
    split_ifs <;> ring
  simp only [he] at h
  exact h.trans_eq (by ring)

theorem source_cubic_conductor_reduction (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Icc 1 X,
      if d ∣ q then (d : ℝ)*Real.sqrt d/(q.totient : ℝ)^2 else 0) ≤
      ((d : ℝ)*Real.sqrt d/(d.totient : ℝ)^2) * totientMass (X/d) := by
  have h := mul_le_mul_of_nonneg_left (totient_multiples X hd)
    (show 0 ≤ (d : ℝ)*Real.sqrt d by positivity)
  rw [mul_sum] at h
  have he (q : ℕ) : (d : ℝ)*Real.sqrt d *
      (if d ∣ q then 1/(q.totient : ℝ)^2 else 0) =
      (if d ∣ q then (d : ℝ)*Real.sqrt d/(q.totient : ℝ)^2 else 0) := by
    split_ifs <;> ring
  simp only [he] at h
  exact h.trans_eq (by ring)

end LiuWang.Proof.SourceRoute.MajorException
