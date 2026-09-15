import LiuWang.Proof.GlobalZeroDensity.Sharp.Pointwise

/-! Finite exponential means: exact diagonal extraction and oscillatory off-diagonal payment. -/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

def wave (w t : ℝ) : ℂ := Complex.exp ((w : ℂ) * Complex.I * t)

def exponentialPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * wave (w n) t

theorem norm_wave (w t : ℝ) : ‖wave w t‖ = 1 := by
  simp [wave, Complex.norm_exp]

theorem wave_mul_conj (v w t : ℝ) :
    wave v t * conj (wave w t) = wave (v - w) t := by
  simp only [wave, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem wave_integral_bound {w : ℝ} (hw : w ≠ 0) (u : ℝ) :
    ‖∫ t in -u..u, wave w t‖ ≤ 2 / |w| := by
  have hc : (w : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hw) Complex.I_ne_zero
  unfold wave
  rw [integral_exp_mul_complex hc, norm_div]
  have h := norm_sub_le (Complex.exp ((w : ℂ) * Complex.I * u))
    (Complex.exp ((w : ℂ) * Complex.I * (-u)))
  have hnorm : ‖(w : ℂ) * Complex.I‖ = |w| := by simp
  rw [hnorm]
  have he : ‖Complex.exp ((w : ℂ) * Complex.I * u) -
      Complex.exp ((w : ℂ) * Complex.I * (-u))‖ ≤ 2 := by
    simpa [Complex.norm_exp, one_add_one_eq_two] using h
  simpa only [Complex.ofReal_neg] using div_le_div_of_nonneg_right he (abs_nonneg w)

theorem polynomial_sq_expansion (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (t : ℝ) :
    ((‖exponentialPolynomial S a w t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, a m * conj (a n) * wave (w m - w n) t := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  simp only [exponentialPolynomial, map_sum, map_mul, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  rw [show a m * wave (w m) t * (conj (a n) * conj (wave (w n) t)) =
    (a m * conj (a n)) * (wave (w m) t * conj (wave (w n) t)) by ring,
    wave_mul_conj]

theorem polynomial_integral_expansion
    (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (u : ℝ) :
    ((∫ t in -u..u, ‖exponentialPolynomial S a w t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S,
        a m * conj (a n) * ∫ t in -u..u, wave (w m - w n) t := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [polynomial_sq_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro m _
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro n _
      exact intervalIntegral.integral_const_mul _ _
    · intro n _
      apply Continuous.intervalIntegrable
      unfold wave
      fun_prop
  · intro m _
    apply Continuous.intervalIntegrable
    unfold wave
    fun_prop

theorem finite_mean_le (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (hw : Set.InjOn w S) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in -u..u, ‖exponentialPolynomial S a w t‖ ^ 2) ≤
      2 * u * ∑ n ∈ S, ‖a n‖ ^ 2 +
      2 * ∑ m ∈ S, ∑ n ∈ S.erase m, ‖a m‖ * ‖a n‖ / |w m - w n| := by
  calc
    _ ≤ ‖((∫ t in -u..u, ‖exponentialPolynomial S a w t‖ ^ 2 : ℝ) : ℂ)‖ :=
      Complex.re_le_norm _
    _ = ‖∑ m ∈ S, ∑ n ∈ S,
        a m * conj (a n) * ∫ t in -u..u, wave (w m - w n) t‖ := by
      rw [polynomial_integral_expansion]
    _ ≤ ∑ m ∈ S, (2 * u * ‖a m‖ ^ 2 +
        2 * ∑ n ∈ S.erase m, ‖a m‖ * ‖a n‖ / |w m - w n|) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro m hm
      rw [← sum_erase_add _ _ hm]
      apply (norm_add_le _ _).trans
      have hd : ‖a m * conj (a m) * ∫ t in -u..u, wave (w m - w m) t‖ =
          2 * u * ‖a m‖ ^ 2 := by
        have hz : (∫ t in -u..u, wave 0 t) = ((2 * u : ℝ) : ℂ) := by
          simp [wave, two_mul]
        rw [sub_self, hz, norm_mul, norm_mul, norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : 0 ≤ 2 * u)]
        ring
      rw [hd]
      have ho : ‖∑ n ∈ S.erase m,
          a m * conj (a n) * ∫ t in -u..u, wave (w m - w n) t‖ ≤
          2 * ∑ n ∈ S.erase m, ‖a m‖ * ‖a n‖ / |w m - w n| := by
        apply (norm_sum_le _ _).trans
        rw [mul_sum]
        apply sum_le_sum
        intro n hn
        have hmn : w m - w n ≠ 0 := by
          intro he
          have he' := hw hm (mem_erase.mp hn).2 (sub_eq_zero.mp he)
          exact (mem_erase.mp hn).1 he'.symm
        have hb := mul_le_mul_of_nonneg_left (wave_integral_bound hmn u)
          (mul_nonneg (norm_nonneg (a m)) (norm_nonneg (a n)))
        simpa only [norm_mul, norm_conj, div_eq_mul_inv, mul_assoc, mul_comm,
          mul_left_comm] using hb
      linarith
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]

end LiuWang.Proof.GlobalZeroDensity.Sharp
