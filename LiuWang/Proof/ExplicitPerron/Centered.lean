import LiuWang.Proof.ExplicitPerron.Characters

/-!
# Actual centered integrand and independently chosen heights

The change from `[-T,T]` to `[Hminus,Hplus]` is charged as two short vertical
segments. No symmetry of the selected heights is asserted or used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.ExplicitPerron

open BombieriVinogradov.SiegelWalfisz

theorem continuous_characterIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x b : ℝ} (hx : 0 < x) (hb : 1 < b) :
    Continuous (fun u : ℝ => characterIntegrand chi x (b + u * Complex.I)) := by
  have hs := twisted_summable chi (s := (b : ℂ)) (by simpa using hb)
  have h := continuous_tsum
    (term_continuous (twistedMangoldtSequence chi) hx (zero_lt_one.trans hb))
    (hs.norm.mul_left (x ^ b / b))
    (norm_term_le (twistedMangoldtSequence chi) hx (zero_lt_one.trans hb))
  convert h using 1
  funext u
  rw [characterIntegrand_eq_series chi x (by simpa using hb)]
  simp only [seriesIntegrand, LSeries, term, tsum_mul_right]

theorem centeredIntegrand_eq_sub {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x y : ℝ) (s : ℂ) :
    centeredIntegrand chi x y s =
      characterIntegrand chi x s - characterIntegrand chi y s := by
  unfold centeredIntegrand characterIntegrand
  ring

theorem continuous_centeredIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x y b : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hb : 1 < b) :
    Continuous (fun u : ℝ => centeredIntegrand chi x y (b + u * Complex.I)) := by
  simp_rw [centeredIntegrand_eq_sub]
  exact (continuous_characterIntegrand chi hx hb).sub
    (continuous_characterIntegrand chi hy hb)

theorem centered_vertical_eq_sub {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x y b : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hb : 1 < b) (lo hi : ℝ) :
    vertical (centeredIntegrand chi x y) b lo hi =
      vertical (characterIntegrand chi x) b lo hi -
        vertical (characterIntegrand chi y) b lo hi := by
  simp only [vertical, centeredIntegrand_eq_sub]
  rw [intervalIntegral.integral_sub
    ((continuous_characterIntegrand chi hx hb).intervalIntegrable lo hi)
    ((continuous_characterIntegrand chi hy hb).intervalIntegrable lo hi), mul_sub]

theorem norm_centered_perron_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x y b T : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxn : ∀ n : ℕ, x ≠ n) (hyn : ∀ n : ℕ, y ≠ n)
    (hb : 1 < b) (hT : 0 < T) :
    ‖vertical (centeredIntegrand chi x y) b (-T) T - (psi chi x - psi chi y)‖ ≤
      effectiveError x b T + effectiveError y b T := by
  rw [centered_vertical_eq_sub chi hx hy hb]
  have heq :
      vertical (characterIntegrand chi x) b (-T) T -
          vertical (characterIntegrand chi y) b (-T) T - (psi chi x - psi chi y) =
        (vertical (characterIntegrand chi x) b (-T) T - psi chi x) -
          (vertical (characterIntegrand chi y) b (-T) T - psi chi y) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_character_perron_le chi hx hxn hb hT)
    (norm_character_perron_le chi hy hyn hb hT))

theorem psi_two_half {q : ℕ} (chi : DirichletCharacter ℂ q) :
    psi chi (5 / 2) = (Real.log 2 : ℂ) * chi 2 := by
  rw [psi_eq_sum]
  norm_num [Finset.sum_Icc_succ_top, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

theorem norm_psi_two_half_le {q : ℕ} (chi : DirichletCharacter ℂ q) :
    ‖psi chi (5 / 2)‖ ≤ Real.log 2 := by
  rw [psi_two_half, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg (by norm_num))]
  exact mul_le_of_le_one_right (Real.log_nonneg (by norm_num)) (chi.norm_le_one _)

theorem norm_vertical_le_const (f : ℂ → ℂ) (b lo hi K : ℝ)
    (h : ∀ u ∈ Ι lo hi, ‖f (b + u * Complex.I)‖ ≤ K) :
    ‖vertical f b lo hi‖ ≤ K * |hi - lo| / (2 * Real.pi) := by
  rw [vertical, norm_mul]
  have hnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hnorm]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (K * |hi - lo|) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_of_norm_le_const h) (by positivity)
    _ = _ := by ring

theorem norm_centeredIntegrand_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x y b H u : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hb : 1 < b) (hH : 0 < H) (hu : H ≤ |u|) :
    ‖centeredIntegrand chi x y (b + u * Complex.I)‖ ≤
      ((Real.log 4 + 4) * b / (b - 1)) * (x ^ b + y ^ b) / H := by
  have hr : ((b : ℂ) + u * Complex.I).re = b := by simp
  have hden : H ≤ ‖(b : ℂ) + u * Complex.I‖ :=
    hu.trans (by simpa using Complex.abs_im_le_norm ((b : ℂ) + u * Complex.I))
  rw [centeredIntegrand, norm_div, norm_mul]
  have hpow : ‖(x : ℂ) ^ ((b : ℂ) + u * Complex.I) -
      (y : ℂ) ^ ((b : ℂ) + u * Complex.I)‖ ≤ x ^ b + y ^ b := by
    simpa only [Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_cpow_eq_rpow_re_of_pos hy, hr] using
      norm_sub_le ((x : ℂ) ^ ((b : ℂ) + u * Complex.I))
        ((y : ℂ) ^ ((b : ℂ) + u * Complex.I))
  have hlog := norm_logDeriv_le chi (s := (b : ℂ) + u * Complex.I) (by simpa using hb)
  rw [hr] at hlog
  gcongr

def heightCorrection (x y b T : ℝ) : ℝ :=
  ((Real.log 4 + 4) * b / (b - 1)) * (x ^ b + y ^ b) / (Real.pi * (T - 1))

theorem norm_asymmetric_sub_symmetric_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x y b T Hminus Hplus : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hb : 1 < b) (hT : 1 < T)
    (hminus : |Hminus + T| ≤ 1) (hplus : |Hplus - T| ≤ 1) :
    ‖vertical (centeredIntegrand chi x y) b Hminus Hplus -
      vertical (centeredIntegrand chi x y) b (-T) T‖ ≤ heightCorrection x y b T := by
  let f := centeredIntegrand chi x y
  let K := ((Real.log 4 + 4) * b / (b - 1)) * (x ^ b + y ^ b) / (T - 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc := continuous_centeredIntegrand chi hx hy hb
  have heq : vertical f b Hminus Hplus - vertical f b (-T) T =
      vertical f b T Hplus - vertical f b (-T) Hminus := by
    simp only [vertical, ← mul_sub]
    congr 1
    exact intervalIntegral.integral_interval_sub_interval_comm'
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hp : ‖vertical f b T Hplus‖ ≤ K / (2 * Real.pi) := by
    apply (norm_vertical_le_const f b T Hplus K ?_).trans
    · exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    · intro u hu
      apply norm_centeredIntegrand_le chi hx hy hb (by linarith)
      have h : min T Hplus < u := hu.1
      have hmin : T - 1 ≤ min T Hplus := le_min (by linarith) (by
        have := (abs_le.mp hplus).1
        linarith)
      exact (hmin.trans h.le).trans (le_abs_self _)
  have hm : ‖vertical f b (-T) Hminus‖ ≤ K / (2 * Real.pi) := by
    apply (norm_vertical_le_const f b (-T) Hminus K ?_).trans
    · have heq : Hminus - -T = Hminus + T := by ring
      rw [heq]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    · intro u hu
      apply norm_centeredIntegrand_le chi hx hy hb (by linarith)
      have h : u ≤ max (-T) Hminus := hu.2
      have hmax : max (-T) Hminus ≤ -(T - 1) := max_le (by linarith) (by
        have := (abs_le.mp hminus).2
        linarith)
      exact (by linarith : T - 1 ≤ -u).trans (neg_le_abs _)
  rw [heq]
  calc
    _ ≤ ‖vertical f b T Hplus‖ + ‖vertical f b (-T) Hminus‖ := norm_sub_le _ _
    _ ≤ K / (2 * Real.pi) + K / (2 * Real.pi) := add_le_add hp hm
    _ = heightCorrection x y b T := by
      dsimp [K, heightCorrection]
      field_simp
      norm_num

theorem norm_asymmetric_centered_perron_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x b T Hminus Hplus : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 1 < b) (hT : 1 < T)
    (hminus : |Hminus + T| ≤ 1) (hplus : |Hplus - T| ≤ 1) :
    ‖vertical (centeredIntegrand chi x (5 / 2)) b Hminus Hplus - psi chi x‖ ≤
      effectiveError x b T + effectiveError (5 / 2) b T + Real.log 2 +
        heightCorrection x (5 / 2) b T := by
  have hs := norm_centered_perron_le chi hx (by norm_num : (0 : ℝ) < 5 / 2) hxn
    (by intro n; convert halfInteger_ne_nat 2 n using 1; norm_num) hb (zero_lt_one.trans hT)
  have ha := norm_asymmetric_sub_symmetric_le chi hx (by norm_num : (0 : ℝ) < 5 / 2)
    hb hT hminus hplus
  have heq :
      vertical (centeredIntegrand chi x (5 / 2)) b Hminus Hplus - psi chi x =
        (vertical (centeredIntegrand chi x (5 / 2)) b Hminus Hplus -
          vertical (centeredIntegrand chi x (5 / 2)) b (-T) T) +
        (vertical (centeredIntegrand chi x (5 / 2)) b (-T) T -
          (psi chi x - psi chi (5 / 2))) - psi chi (5 / 2) := by ring
  rw [heq]
  calc
    _ ≤
        ‖vertical (centeredIntegrand chi x (5 / 2)) b Hminus Hplus -
          vertical (centeredIntegrand chi x (5 / 2)) b (-T) T‖ +
        ‖vertical (centeredIntegrand chi x (5 / 2)) b (-T) T -
          (psi chi x - psi chi (5 / 2))‖ + ‖psi chi (5 / 2)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith [norm_psi_two_half_le chi]

end LiuWang.Proof.ExplicitPerron
