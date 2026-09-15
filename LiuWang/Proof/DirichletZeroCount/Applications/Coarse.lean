import LiuWang.Proof.DirichletZeroCount.Family

/-! # A full-family count budget for the density theorem's low-alpha branch -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount.Applications

theorem log_height_ge_eight {y : ℝ} (hy : 10000 ≤ y) : 8 ≤ Real.log y := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < y)).mpr
  calc
    Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 3 ^ (8 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
    _ ≤ y := by norm_num; linarith

theorem log_product_ge_eight {q y : ℝ} (hq : 1 ≤ q) (hy : 10000 ≤ y) :
    8 ≤ Real.log (q * y) :=
  (log_height_ge_eight hy).trans
    (Real.log_le_log (by linarith) (le_mul_of_one_le_left (by linarith) hq))

theorem log_shift_le {q y c : ℝ} (hq : 1 ≤ q) (hy : 10000 ≤ y)
    (hc : 0 ≤ c) (hc4 : c ≤ 4) :
    Real.log (y + c) ≤ Real.log (q * y) + 1 := by
  have h := Real.log_le_log (by linarith : 0 < y + c)
    (by linarith : y + c ≤ 2 * y)
  rw [Real.log_mul (by norm_num) (by linarith : y ≠ 0)] at h
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hly := Real.log_le_log (by linarith : 0 < y)
    (le_mul_of_one_le_left (by linarith : 0 ≤ y) hq)
  linarith

theorem nonprincipalBound_le_ten {q : ℕ} [NeZero q] {y : ℝ}
    (hy : 10000 ≤ y) :
    nonprincipalBound q y ≤ 10 * y * Real.log ((q : ℝ) * y) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hS := log_product_ge_eight hq hy
  have hlq : Real.log q ≤ Real.log ((q : ℝ) * y) :=
    Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) (by linarith))
  have hls := log_shift_le hq hy (c := 3) (by norm_num) (by norm_num)
  have hb : Real.log q / 2 + Real.log (y + 3) / 2 + 5 / 4 ≤
      3 * Real.log ((q : ℝ) * y) := by linarith
  have hb0 : 0 ≤ Real.log q / 2 + Real.log (y + 3) / 2 + 5 / 4 := by
    have h1 := Real.log_nonneg hq
    have h2 := Real.log_nonneg (by linarith : 1 ≤ y + 3)
    linarith
  calc
    nonprincipalBound q y ≤ (3 * y) * (3 * Real.log ((q : ℝ) * y)) :=
      mul_le_mul (by linarith) hb hb0 (by linarith)
    _ ≤ 10 * y * Real.log ((q : ℝ) * y) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ y) (by linarith : 0 ≤ Real.log ((q : ℝ) * y))]

theorem principalBound_le_ten {q : ℕ} [NeZero q] {y : ℝ}
    (hy : 10000 ≤ y) :
    principalBound y ≤ 10 * y * Real.log ((q : ℝ) * y) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hS := log_product_ge_eight hq hy
  have hls := log_shift_le hq hy (c := 4) (by norm_num) (by norm_num)
  have hi : 1 / (y + 3) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hb : Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3 ≤
      3 * Real.log ((q : ℝ) * y) := by linarith
  have hb0 : 0 ≤ Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3 := by
    have h := Real.log_nonneg (by linarith : 1 ≤ y + 4)
    positivity
  calc
    principalBound y ≤
        (2 * y + 4) * (Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3) := by
      rw [principalBound, if_neg (by linarith)]
      exact min_le_right _ _
    _ ≤ (3 * y) * (3 * Real.log ((q : ℝ) * y)) :=
      mul_le_mul (by linarith) hb hb0 (by linarith)
    _ ≤ 10 * y * Real.log ((q : ℝ) * y) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ y) (by linarith : 0 ≤ Real.log ((q : ℝ) * y))]

theorem familyCount_le_ten (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 10000 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ 10 * q * y * Real.log ((q : ℝ) * y) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hphi : 1 ≤ q.totient := Nat.totient_pos.mpr hq
  have hsub : (q.totient - 1 : ℕ) + 1 = q.totient := Nat.sub_add_cancel hphi
  have hcast : ((q.totient - 1 : ℕ) : ℝ) + 1 = q.totient := by exact_mod_cast hsub
  have hS := log_product_ge_eight (Nat.one_le_cast.mpr hq) hy
  have hB : 0 ≤ 10 * y * Real.log ((q : ℝ) * y) := by positivity
  calc
    (familyCount q alpha y : ℝ) ≤
        principalBound y + (q.totient - 1 : ℕ) * nonprincipalBound q y :=
      (familyCount_le q alpha (by linarith)).trans (familyBound_le_modulus q (by linarith))
    _ ≤ 10 * y * Real.log ((q : ℝ) * y) +
        (q.totient - 1 : ℕ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      add_le_add (principalBound_le_ten (q := q) hy)
        (mul_le_mul_of_nonneg_left (nonprincipalBound_le_ten hy) (Nat.cast_nonneg _))
    _ = q.totient * (10 * y * Real.log ((q : ℝ) * y)) := by
      rw [← hcast]
      ring
    _ ≤ (q : ℝ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.totient_le q)) hB
    _ = _ := by ring

end LiuWang.Proof.DirichletZeroCount.Applications
