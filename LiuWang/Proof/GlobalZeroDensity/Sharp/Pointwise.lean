import LiuWang.Proof.GlobalZeroDensity.Sharp.ZetaCritical

/-! A stronger same-domain critical-line detector bound and the printed Lemma 3.2. -/

set_option autoImplicit false

noncomputable section

open Complex

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

def sourceCoefficient (t : ℝ) : ℝ :=
  if |t| < 1 / 2 then 320745 / 10000
  else if |t| < 1 then 180559 / 10000 else 14272 / 1000

theorem F_critical_sharp {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤ 24 * y * (1 + |t|) := by
  let p := Real.sqrt y * Real.sqrt (1 + |t|)
  have hy0 : 0 ≤ y := by linarith
  have hu0 : 0 ≤ 1 + |t| := by positivity
  have hyroot : 100 ≤ Real.sqrt y := by
    have h := Real.sqrt_le_sqrt hy
    norm_num at h
    exact h
  have huroot : 1 ≤ Real.sqrt (1 + |t|) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + |t| by linarith [abs_nonneg t])
    simpa only [Real.sqrt_one] using h
  have hp : 100 ≤ p := by
    dsimp [p]
    nlinarith
  have hp2 : p ^ 2 = y * (1 + |t|) := by
    simp only [p, mul_pow, Real.sq_sqrt hy0, Real.sq_sqrt hu0]
  have h := norm_sub_le
    (riemannZeta ((1 / 2 : ℂ) + t * Complex.I) *
      Q y ((1 / 2 : ℂ) + t * Complex.I)) 1
  rw [norm_mul, norm_one] at h
  have hm := mul_le_mul (norm_zeta_sqrt_height t) (norm_Q_eight_fifths hy t)
    (norm_nonneg _) (by positivity)
  have hf : ‖f y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ (481 / 100) * p := by
    change ‖riemannZeta _ * Q y _ - 1‖ ≤ _
    dsimp [p] at hp ⊢
    nlinarith
  have hf2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
  change ‖f y _‖ ^ 2 ≤ _
  rw [mul_pow, hp2] at hf2
  nlinarith [mul_nonneg hy0 hu0]

theorem source_coefficient_payment (t : ℝ) :
    24 * (1 + |t|) ≤
      sourceCoefficient t * (1 / 2 + |t|) * (2583 / 1000) := by
  unfold sourceCoefficient
  split_ifs with h0 h1
  · nlinarith [abs_nonneg t]
  · have ht : 1 / 2 ≤ |t| := le_of_not_gt h0
    nlinarith
  · have ht : 1 ≤ |t| := le_of_not_gt h1
    nlinarith

theorem source_coefficient_pos (t : ℝ) : 0 < sourceCoefficient t := by
  unfold sourceCoefficient
  split_ifs <;> norm_num

theorem lemma_3_2_of_ten_thousand {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤
      sourceCoefficient t * (1 / 2 + |t|) *
        ((2583 / 1000) * y + (608 / 1000) * Real.log y + 5608 / 1000) := by
  have hy0 : 0 ≤ y := by linarith
  have hl := Real.log_nonneg (show 1 ≤ y by linarith)
  have hpay := mul_le_mul_of_nonneg_right (source_coefficient_payment t) hy0
  have hfac : 0 ≤ sourceCoefficient t * (1 / 2 + |t|) :=
    mul_nonneg (source_coefficient_pos t).le (by positivity)
  have hextra := mul_nonneg hfac
    (show 0 ≤ (608 / 1000) * Real.log y + 5608 / 1000 by linarith)
  have h := F_critical_sharp hy t
  nlinarith

theorem log_six_ge_one : 1 ≤ Real.log 6 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 6)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hm
  norm_num at h hm
  linarith

theorem lemma_3_2 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) (t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤
      sourceCoefficient t * (1 / 2 + |t|) *
        ((2583 / 1000) * y + (608 / 1000) * Real.log y + 5608 / 1000) :=
  lemma_3_2_of_ten_thousand (by linarith [log_six_ge_one]) t

end LiuWang.Proof.GlobalZeroDensity.Sharp
