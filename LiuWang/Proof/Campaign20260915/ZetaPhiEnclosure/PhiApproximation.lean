import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.SincApproximation

set_option autoImplicit false
noncomputable section

open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaValidation

structure RationalBall where
  center : ℚ
  radius : ℚ

def RationalBall.Contains (b : RationalBall) (x : ℝ) : Prop :=
  |x - (b.center : ℝ)| ≤ (b.radius : ℝ)

def phiNumeratorApprox (n : ℕ) (p r : ℚ) : ℚ :=
  sincApprox n (p / 2 * (r ^ 2 - 1 / 4))

def phiDenominatorApprox (n : ℕ) (p r : ℚ) : ℚ :=
  p * (sincApprox n (p / 2 * (r + 1 / 2)) * sincApprox n (p / 2 * (r - 1 / 2)))

def phiSafeDenominator (n : ℕ) (p r : ℚ) : ℚ :=
  max (1 / 24) (phiDenominatorApprox n p r)

def phiNumeratorError (n : ℕ) (p ep r : ℚ) : ℚ :=
  sincError n (p / 2 * (r ^ 2 - 1 / 4)) (ep / 2 * |r ^ 2 - 1 / 4|)

def phiDenominatorError (n : ℕ) (p ep r : ℚ) : ℚ :=
  ep + |p| *
    (sincError n (p / 2 * (r + 1 / 2)) (ep / 2 * |r + 1 / 2|) +
      |sincApprox n (p / 2 * (r + 1 / 2))| *
        sincError n (p / 2 * (r - 1 / 2)) (ep / 2 * |r - 1 / 2|))

def phiApprox (n : ℕ) (p ep r d : ℚ) : RationalBall :=
  let q := phiNumeratorApprox n p r / phiSafeDenominator n p r
  ⟨q, 12 * (phiNumeratorError n p ep r + |q| * phiDenominatorError n p ep r) +
    (derivativeBudget 1 : ℚ) * d⟩

theorem sinc_argument_error (p ep a : ℚ) (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ)) :
    |Real.pi / 2 * (a : ℝ) - ((p / 2 * a : ℚ) : ℝ)| ≤
      ((ep / 2 * |a| : ℚ) : ℝ) := by
  push_cast
  rw [show Real.pi / 2 * (a : ℝ) - (p : ℝ) / 2 * a =
    (Real.pi - p) / 2 * a by ring, abs_mul, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp (by norm_num)) (abs_nonneg _)

theorem phi_numerator_error (n : ℕ) (p ep r : ℚ)
    (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ)) :
    |Real.sinc (Real.pi / 2 * ((r : ℝ) ^ 2 - 1 / 4)) -
      (phiNumeratorApprox n p r : ℝ)| ≤ (phiNumeratorError n p ep r : ℝ) := by
  have h := sincApprox_error n (p / 2 * (r ^ 2 - 1 / 4))
    (ep / 2 * |r ^ 2 - 1 / 4|) (sinc_argument_error p ep (r ^ 2 - 1 / 4) hp)
  simpa only [phiNumeratorApprox, phiNumeratorError, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem phi_denominator_error (n : ℕ) (p ep r : ℚ)
    (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ)) :
    |Real.pi * (Real.sinc (Real.pi / 2 * ((r : ℝ) + 1 / 2)) *
      Real.sinc (Real.pi / 2 * ((r : ℝ) - 1 / 2))) -
      (phiDenominatorApprox n p r : ℝ)| ≤ (phiDenominatorError n p ep r : ℝ) := by
  let a := Real.sinc (Real.pi / 2 * ((r : ℝ) + 1 / 2))
  let b := Real.sinc (Real.pi / 2 * ((r : ℝ) - 1 / 2))
  let A : ℝ := sincApprox n (p / 2 * (r + 1 / 2))
  let B : ℝ := sincApprox n (p / 2 * (r - 1 / 2))
  let ea : ℝ := sincError n (p / 2 * (r + 1 / 2)) (ep / 2 * |r + 1 / 2|)
  let eb : ℝ := sincError n (p / 2 * (r - 1 / 2)) (ep / 2 * |r - 1 / 2|)
  have ha : |a - A| ≤ ea := by
    simpa only [a, A, ea, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      sincApprox_error n (p / 2 * (r + 1 / 2)) (ep / 2 * |r + 1 / 2|)
        (sinc_argument_error p ep (r + 1 / 2) hp)
  have hb : |b - B| ≤ eb := by
    simpa only [b, B, eb, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      sincApprox_error n (p / 2 * (r - 1 / 2)) (ep / 2 * |r - 1 / 2|)
        (sinc_argument_error p ep (r - 1 / 2) hp)
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sinc_le_one _) (Real.abs_sinc_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have he : |a * b - A * B| ≤ ea + |A| * eb := by
    rw [show a * b - A * B = (a - A) * b + A * (b - B) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      ((mul_le_mul ha (Real.abs_sinc_le_one _) (abs_nonneg _) ((abs_nonneg _).trans ha)).trans_eq
        (mul_one _))
      (mul_le_mul_of_nonneg_left hb (abs_nonneg A))
  change |Real.pi * (a * b) - (phiDenominatorApprox n p r : ℝ)| ≤ _
  have hcast : (phiDenominatorApprox n p r : ℝ) = (p : ℝ) * (A * B) := by
    simp only [phiDenominatorApprox, Rat.cast_mul, A, B]
  rw [hcast, show Real.pi * (a * b) - (p : ℝ) * (A * B) =
    (Real.pi - p) * (a * b) + p * (a * b - A * B) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  have h := add_le_add
    ((mul_le_mul hp hab (abs_nonneg _) ((abs_nonneg _).trans hp)).trans_eq (mul_one _))
    (mul_le_mul_of_nonneg_left he (abs_nonneg (p : ℝ)))
  simpa only [phiDenominatorError, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, ea, eb, A,
    abs_mul] using h

theorem clamp_error {D a e c : ℝ} (hc : c ≤ D) (ha : |D - a| ≤ e) :
    |D - max c a| ≤ e := by
  have he : 0 ≤ e := (abs_nonneg _).trans ha
  rw [abs_le] at ha ⊢
  constructor
  · have hmax : max c a ≤ D + e := max_le (by linarith) (by linarith)
    linarith
  · have hm := le_max_right c a
    linarith

theorem phiApprox_correct (n : ℕ) (p ep r d : ℚ) {z : ℝ}
    (hp : |Real.pi - (p : ℝ)| ≤ (ep : ℝ))
    (hr : |(r : ℝ)| ≤ 1) (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (phiApprox n p ep r d).Contains (rsPhi z) := by
  let D := Real.pi * (Real.sinc (Real.pi / 2 * ((r : ℝ) + 1 / 2)) *
    Real.sinc (Real.pi / 2 * ((r : ℝ) - 1 / 2)))
  let N := Real.sinc (Real.pi / 2 * ((r : ℝ) ^ 2 - 1 / 4))
  let S : ℝ := phiSafeDenominator n p r
  let q : ℝ := phiNumeratorApprox n p r / phiSafeDenominator n p r
  have hD : 1 / 12 ≤ D := by
    have h := rsPhi_denominator_lower hr
    dsimp [D]
    linarith [Real.pi_gt_three]
  have hS : 0 < S := by
    have h : (0 : ℚ) < phiSafeDenominator n p r :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    change 0 < (phiSafeDenominator n p r : ℝ)
    exact_mod_cast h
  have hden : |D - S| ≤ (phiDenominatorError n p ep r : ℝ) := by
    have h := clamp_error (by linarith : (1 : ℝ) / 24 ≤ D)
      (phi_denominator_error n p ep r hp)
    simpa only [S, phiSafeDenominator, Rat.cast_max, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using h
  have hnum := phi_numerator_error n p ep r hp
  have hq : (phiNumeratorApprox n p r : ℝ) = q * S := by
    dsimp [q, S]
    exact (div_mul_cancel₀ _ hS.ne').symm
  have he : |rsPhi (r : ℝ) - q| ≤
      12 * ((phiNumeratorError n p ep r : ℝ) + |q| * (phiDenominatorError n p ep r : ℝ)) := by
    have heq : rsPhi (r : ℝ) - q = (N - q * D) / D := by
      change N / D - q = _
      field_simp
    rw [heq, abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) hD)]
    have h : |N - q * D| ≤
        (phiNumeratorError n p ep r : ℝ) + |q| * (phiDenominatorError n p ep r : ℝ) := by
      rw [show N - q * D = (N - q * S) + q * (S - D) by ring]
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_sub_comm S D, ← hq]
      exact add_le_add hnum (mul_le_mul_of_nonneg_left hden (abs_nonneg q))
    have hb := div_le_div₀ ((abs_nonneg _).trans h) h
      (by norm_num : (0 : ℝ) < 1 / 12) hD
    exact hb.trans_eq (by ring)
  have hi := rsPhi_derivative_input_error 0 hz hr he hd
  simpa only [RationalBall.Contains, phiApprox, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_abs, Rat.cast_natCast, Rat.cast_ofNat, q, iteratedDeriv_zero] using hi

def piApprox : ℚ := 314159265358979323846 / 100000000000000000000
def piError : ℚ := 1 / 100000000000000000000

theorem piApprox_correct : |Real.pi - (piApprox : ℝ)| ≤ (piError : ℝ) := by
  rw [abs_le]
  norm_num [piApprox, piError]
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

def phiEnclosure (n : ℕ) (r d : ℚ) : RationalBall := phiApprox n piApprox piError r d

theorem phiEnclosure_correct (n : ℕ) (r d : ℚ) {z : ℝ}
    (hr : |(r : ℝ)| ≤ 1) (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (phiEnclosure n r d).Contains (rsPhi z) :=
  phiApprox_correct n piApprox piError r d piApprox_correct hr hz hd

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
