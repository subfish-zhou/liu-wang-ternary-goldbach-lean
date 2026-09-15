import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalAngle
import Mathlib.Data.Rat.Floor

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

abbrev QComplex := ℚ × ℚ

def realIPower (j : ℕ) : ℚ :=
  if j % 4 = 0 then 1 else if j % 4 = 2 then -1 else 0

def unitTaylor (q : ℚ) : QComplex :=
  (∑ j ∈ Finset.range 12, q ^ j * realIPower j / j.factorial,
   ∑ j ∈ Finset.range 12, q ^ j * imagIPower j / j.factorial)

def roundRational (q : ℚ) : ℚ := (⌊100000000 * q⌋ : ℚ) / 100000000

def roundQComplex (p : QComplex) : QComplex :=
  (roundRational p.1, roundRational p.2)

def squareQComplex (p : QComplex) : QComplex :=
  (p.1 ^ 2 - p.2 ^ 2, 2 * p.1 * p.2)

def unitRepeatedSquare : ℕ → ℚ → QComplex
  | 0, q => roundQComplex (unitTaylor q)
  | k + 1, q => roundQComplex (squareQComplex (unitRepeatedSquare k q))

noncomputable section

open Complex Finset

def QComplex.toComplex (p : QComplex) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

theorem realIPower_correct (j : ℕ) : (realIPower j : ℝ) = (I ^ j).re := by
  rw [I_pow_eq_pow_mod]
  have hj : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold realIPower
  interval_cases h : j % 4 <;> norm_num [h, I_sq, I_pow_three]

theorem unitTaylor_correct (q : ℚ) :
    (unitTaylor q).toComplex = ∑ j ∈ range 12, ((q : ℂ) * I) ^ j / j.factorial := by
  apply Complex.ext
  all_goals
    simp only [QComplex.toComplex, unitTaylor, add_re, add_im, mul_re, mul_im,
      ratCast_re, ratCast_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add, re_sum, im_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, ← ofReal_natCast j.factorial, ← ofReal_ratCast q, ← ofReal_pow]
    simp only [div_ofReal_re, div_ofReal_im, mul_re, mul_im, ofReal_re,
      ofReal_im, zero_mul, sub_zero, add_zero, realIPower_correct, imagIPower_correct]

theorem roundRational_error (q : ℚ) :
    |(roundRational q : ℝ) - (q : ℝ)| ≤ 1 / 100000000 := by
  have hl := Int.floor_le (100000000 * q)
  have hu := Int.lt_floor_add_one (100000000 * q)
  have hlR : (⌊100000000 * q⌋ : ℝ) ≤ 100000000 * (q : ℝ) := by exact_mod_cast hl
  have huR : 100000000 * (q : ℝ) < (⌊100000000 * q⌋ : ℝ) + 1 := by exact_mod_cast hu
  unfold roundRational
  push_cast
  rw [abs_le]
  constructor <;> linarith

theorem roundQComplex_error (p : QComplex) :
    ‖(roundQComplex p).toComplex - p.toComplex‖ ≤ 2 / 100000000 := by
  have h := Complex.norm_le_abs_re_add_abs_im ((roundQComplex p).toComplex - p.toComplex)
  simp only [QComplex.toComplex, roundQComplex, sub_re, sub_im, add_re, add_im,
    mul_re, mul_im, ratCast_re, ratCast_im, I_re, I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_add] at h
  dsimp [roundQComplex, QComplex.toComplex]
  linarith [roundRational_error p.1, roundRational_error p.2]

theorem squareQComplex_correct (p : QComplex) :
    (squareQComplex p).toComplex = p.toComplex ^ 2 := by
  apply Complex.ext <;> simp [QComplex.toComplex, squareQComplex, Complex.mul_re,
    Complex.mul_im, pow_two]
  all_goals ring

theorem unitTaylor_error {q : ℚ} (hq : |q| ≤ 1) :
    ‖exp ((q : ℂ) * I) - (unitTaylor q).toComplex‖ ≤ 1 / 100000000 := by
  have hqR : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have hn : ‖(q : ℂ) * I‖ ≤ 1 := by simpa [norm_mul, Complex.norm_ratCast] using hqR
  rw [unitTaylor_correct]
  have h := Complex.exp_bound' (n := 12) (x := (q : ℂ) * I) (by norm_num; linarith)
  have hp : ‖(q : ℂ) * I‖ ^ 12 ≤ (1 : ℝ) ^ 12 :=
    pow_le_pow_left₀ (norm_nonneg _) hn _
  norm_num at h hp
  linarith

theorem unit_square_error {a b : ℂ} {e : ℝ}
    (ha : ‖a‖ = 1) (he0 : 0 ≤ e) (he1 : e ≤ 1) (he : ‖a - b‖ ≤ e) :
    ‖a ^ 2 - b ^ 2‖ ≤ 3 * e := by
  have hb : ‖b‖ ≤ 1 + e := by
    have h := norm_add_le a (b - a)
    rw [add_sub_cancel, norm_sub_rev b a, ha] at h
    linarith
  have hab : ‖a + b‖ ≤ 2 + e := by
    have h := norm_add_le a b
    rw [ha] at h
    linarith
  calc
    _ = ‖a - b‖ * ‖a + b‖ := by rw [← norm_mul]; congr 1; ring
    _ ≤ e * (2 + e) := mul_le_mul he hab (norm_nonneg _) he0
    _ ≤ _ := by nlinarith

theorem unitRepeatedSquare_error {q : ℚ} (hq : |q| ≤ 1) {k : ℕ} (hk : k ≤ 7) :
    ‖exp (((2 : ℝ) ^ k * (q : ℝ) : ℝ) * I) -
      (unitRepeatedSquare k q).toComplex‖ ≤ (4 * (3 : ℝ) ^ k - 1) / 100000000 := by
  induction k with
  | zero =>
      have ht := unitTaylor_error hq
      have hr := roundQComplex_error (unitTaylor q)
      have h := norm_sub_le_norm_sub_add_norm_sub (exp ((q : ℂ) * I)) (unitTaylor q).toComplex
        (roundQComplex (unitTaylor q)).toComplex
      rw [norm_sub_rev (unitTaylor q).toComplex] at h
      norm_num [unitRepeatedSquare]
      linarith
  | succ k ih =>
      have hk' : k ≤ 7 := by omega
      have he := ih hk'
      have hp : (3 : ℝ) ^ k ≤ 3 ^ 7 := pow_le_pow_right₀ (by norm_num) hk'
      have he0 : 0 ≤ (4 * (3 : ℝ) ^ k - 1) / 100000000 := by
        have h := one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) (n := k)
        linarith
      have he1 : (4 * (3 : ℝ) ^ k - 1) / 100000000 ≤ 1 := by norm_num at hp; linarith
      have hs := unit_square_error
        (Complex.norm_exp_ofReal_mul_I ((2 : ℝ) ^ k * (q : ℝ))) he0 he1 he
      have hid : exp ((((2 : ℝ) ^ (k + 1) * (q : ℝ) : ℝ) : ℂ) * I) =
          exp ((((2 : ℝ) ^ k * (q : ℝ) : ℝ) : ℂ) * I) ^ 2 := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hid, unitRepeatedSquare]
      have hr := roundQComplex_error (squareQComplex (unitRepeatedSquare k q))
      rw [squareQComplex_correct] at hr
      have ht := norm_sub_le_norm_sub_add_norm_sub
        (exp (((2 : ℝ) ^ k * (q : ℝ) : ℝ) * I) ^ 2)
        ((unitRepeatedSquare k q).toComplex ^ 2)
        ((roundQComplex (squareQComplex (unitRepeatedSquare k q))).toComplex)
      rw [norm_sub_rev ((unitRepeatedSquare k q).toComplex ^ 2)] at ht
      rw [pow_succ (3 : ℝ) k]
      linarith

theorem unitRepeatedSquare_seven_error {q : ℚ} (hq : |q| ≤ 1) :
    ‖exp (((128 : ℝ) * (q : ℝ) : ℝ) * I) -
      (unitRepeatedSquare 7 q).toComplex‖ ≤ 1 / 10000 := by
  have h := unitRepeatedSquare_error hq (k := 7) (by norm_num)
  norm_num at h ⊢
  exact h.trans (by norm_num)

#print axioms unitRepeatedSquare_seven_error

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
