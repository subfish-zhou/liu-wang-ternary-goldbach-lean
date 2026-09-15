import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalUnitPhase

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def unitTaylorAt (m : ℕ) (q : ℚ) : QComplex :=
  (∑ j ∈ Finset.range m, q ^ j * realIPower j / j.factorial,
   ∑ j ∈ Finset.range m, q ^ j * imagIPower j / j.factorial)

def roundRationalAt (D : ℕ) (q : ℚ) : ℚ := (⌊(D : ℚ) * q⌋ : ℚ) / D

def roundQComplexAt (D : ℕ) (p : QComplex) : QComplex :=
  (roundRationalAt D p.1, roundRationalAt D p.2)

def unitPhaseAt (D m : ℕ) : ℕ → ℚ → QComplex
  | 0, q => roundQComplexAt D (unitTaylorAt m q)
  | k + 1, q => roundQComplexAt D (squareQComplex (unitPhaseAt D m k q))

noncomputable section
open Complex Finset

theorem unitTaylorAt_correct (m : ℕ) (q : ℚ) :
    (unitTaylorAt m q).toComplex = ∑ j ∈ range m, ((q : ℂ) * I) ^ j / j.factorial := by
  apply Complex.ext
  all_goals
    simp only [QComplex.toComplex, unitTaylorAt, add_re, add_im, mul_re, mul_im,
      ratCast_re, ratCast_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add, re_sum, im_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, ← ofReal_natCast j.factorial, ← ofReal_ratCast q, ← ofReal_pow]
    simp only [div_ofReal_re, div_ofReal_im, mul_re, mul_im, ofReal_re,
      ofReal_im, zero_mul, sub_zero, add_zero, realIPower_correct, imagIPower_correct]

theorem unitTaylorAt_error {m : ℕ} (hm : 1 ≤ m) {q : ℚ} (hq : |q| ≤ 1) :
    ‖exp ((q : ℂ) * I) - (unitTaylorAt m q).toComplex‖ ≤ 2 / (m.factorial : ℝ) := by
  have hn : ‖(q : ℂ) * I‖ ≤ 1 := by
    have hqR : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
    simpa [norm_mul, Complex.norm_ratCast] using hqR
  rw [unitTaylorAt_correct]
  have hr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := Complex.exp_bound' (n := m) (x := (q : ℂ) * I)
    (by rw [div_le_iff₀ (by positivity)]; push_cast; linarith)
  have hp : ‖(q : ℂ) * I‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hn
  apply h.trans
  have hd : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hd hd]
  nlinarith

theorem roundRationalAt_error {D : ℕ} (hD : 1 ≤ D) (q : ℚ) :
    |(roundRationalAt D q : ℝ) - (q : ℝ)| ≤ 1 / (D : ℝ) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hl := Int.floor_le ((D : ℚ) * q)
  have hu := Int.lt_floor_add_one ((D : ℚ) * q)
  have hlR : (⌊(D : ℚ) * q⌋ : ℝ) ≤ (D : ℝ) * q := by exact_mod_cast hl
  have huR : (D : ℝ) * q < (⌊(D : ℚ) * q⌋ : ℝ) + 1 := by exact_mod_cast hu
  unfold roundRationalAt
  push_cast
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hDp]
    have hcancel : (-(1 / (D : ℝ)) + (q : ℝ)) * D = -1 + (q : ℝ) * D := by field_simp
    rw [hcancel]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hDp]
    have hcancel : (1 / (D : ℝ) + (q : ℝ)) * D = 1 + (q : ℝ) * D := by field_simp
    rw [hcancel]
    nlinarith

theorem roundQComplexAt_error {D : ℕ} (hD : 1 ≤ D) (p : QComplex) :
    ‖(roundQComplexAt D p).toComplex - p.toComplex‖ ≤ 2 / (D : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((roundQComplexAt D p).toComplex - p.toComplex)
  simp only [QComplex.toComplex, roundQComplexAt, sub_re, sub_im, add_re, add_im,
    mul_re, mul_im, ratCast_re, ratCast_im, I_re, I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_add] at h
  dsimp [roundQComplexAt, QComplex.toComplex]
  exact (h.trans (add_le_add (roundRationalAt_error hD p.1) (roundRationalAt_error hD p.2))).trans_eq
    (by ring)

theorem unitPhaseAt_error {D m K : ℕ} (hD : 1 ≤ D) (hm : 1 ≤ m)
    (hseed : 2 / (m.factorial : ℝ) ≤ 1 / (D : ℝ))
    (hbudget : (4 * (3 : ℝ) ^ K - 1) / D ≤ 1)
    {q : ℚ} (hq : |q| ≤ 1) {k : ℕ} (hk : k ≤ K) :
    ‖exp ((((2 : ℝ) ^ k * (q : ℝ) : ℝ) : ℂ) * I) -
      (unitPhaseAt D m k q).toComplex‖ ≤ (4 * (3 : ℝ) ^ k - 1) / D := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  induction k with
  | zero =>
    have ht := (unitTaylorAt_error hm hq).trans hseed
    have hr := roundQComplexAt_error hD (unitTaylorAt m q)
    have h := norm_sub_le_norm_sub_add_norm_sub (exp ((q : ℂ) * I)) (unitTaylorAt m q).toComplex
      (roundQComplexAt D (unitTaylorAt m q)).toComplex
    rw [norm_sub_rev (unitTaylorAt m q).toComplex] at h
    norm_num [unitPhaseAt]
    exact (h.trans (add_le_add ht hr)).trans_eq (by ring)
  | succ k ih =>
    have he := ih (by omega)
    have he0 : 0 ≤ (4 * (3 : ℝ) ^ k - 1) / D := by
      apply div_nonneg _ hDp.le
      have hp := one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) (n := k)
      linarith
    have he1 : (4 * (3 : ℝ) ^ k - 1) / D ≤ 1 :=
      (div_le_div_of_nonneg_right
        (by have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) (show k ≤ K by omega)
            linarith) hDp.le).trans hbudget
    have hs := unit_square_error (Complex.norm_exp_ofReal_mul_I ((2 : ℝ) ^ k * (q : ℝ)))
      he0 he1 he
    have hid : exp ((((2 : ℝ) ^ (k + 1) * (q : ℝ) : ℝ) : ℂ) * I) =
        exp ((((2 : ℝ) ^ k * (q : ℝ) : ℝ) : ℂ) * I) ^ 2 := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hid, unitPhaseAt]
    have hr := roundQComplexAt_error hD (squareQComplex (unitPhaseAt D m k q))
    rw [squareQComplex_correct] at hr
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (exp ((((2 : ℝ) ^ k * (q : ℝ) : ℝ) : ℂ) * I) ^ 2)
      ((unitPhaseAt D m k q).toComplex ^ 2)
      ((roundQComplexAt D (squareQComplex (unitPhaseAt D m k q))).toComplex)
    rw [norm_sub_rev ((unitPhaseAt D m k q).toComplex ^ 2)] at ht
    rw [pow_succ (3 : ℝ) k]
    have hid : (4 * ((3 : ℝ) ^ k * 3) - 1) / D =
        3 * ((4 * (3 : ℝ) ^ k - 1) / D) + 2 / D := by ring
    rw [hid]
    linarith

theorem unitPhaseAt_original_scale {q : ℚ} (hq : |q| ≤ 1) {k : ℕ} (hk : k ≤ 32) :
    ‖exp ((((2 : ℝ) ^ k * (q : ℝ) : ℝ) : ℂ) * I) -
      (unitPhaseAt (10 ^ 40) 40 k q).toComplex‖ ≤ 1 / (10 : ℝ) ^ 24 := by
  have h := unitPhaseAt_error (D := 10 ^ 40) (m := 40) (K := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq hk
  have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) hk
  norm_num at hp h ⊢
  linarith

#print axioms unitPhaseAt_error
#print axioms unitPhaseAt_original_scale

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
