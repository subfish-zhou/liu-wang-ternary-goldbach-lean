import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.CorrectionEnclosures
import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorGaussianTail

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem correctionMoment_truncation (n : ℕ) {z d : ℝ} (hz : |z| ≤ 1) (hd : 0 < d) :
    ‖correctionMoment n z -
      ∫ t : ℝ in Ioc (-d) d, (siegelLine t - ((z : ℂ) + 1) / 2) ^ n * correctionKernel z t‖ ≤
        (108 * (n.factorial : ℝ)) * Real.exp (-Real.pi * d ^ 2) / (Real.pi * d) := by
  have hf := correctionCenteredKernel_integrable n (z : ℂ)
  have hi := integral_add_compl (s := Ioc (-d) d) measurableSet_Ioc hf
  have he : correctionMoment n z -
      ∫ t : ℝ in Ioc (-d) d, (siegelLine t - ((z : ℂ) + 1) / 2) ^ n * correctionKernel z t =
      ∫ t : ℝ in (Ioc (-d) d)ᶜ, (siegelLine t - ((z : ℂ) + 1) / 2) ^ n * correctionKernel z t := by
    unfold correctionMoment
    linear_combination -hi
  rw [he]
  apply exterior_integral_bound _ (by positivity) Real.pi_pos hd
    (fun t _ => correction_moment_kernel_bound n hz t)
  unfold correctionKernel siegelLine
  fun_prop

def momentTailBudget (n m : ℕ) (d : ℚ) : ℚ :=
  108 * n.factorial * m.factorial / (3 * d * (3 * d ^ 2) ^ m)

theorem correctionMoment_rational_truncation (n m : ℕ) {z : ℝ} (hz : |z| ≤ 1)
    (d : ℚ) (hd : 0 < d) :
    ‖correctionMoment n z -
      ∫ t : ℝ in Ioc (-(d : ℝ)) d,
        (siegelLine t - ((z : ℂ) + 1) / 2) ^ n * correctionKernel z t‖ ≤
      (momentTailBudget n m d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < 3 * (d : ℝ) ^ 2 := by positivity
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have he : Real.exp (-(3 * (d : ℝ) ^ 2)) ≤
      (m.factorial : ℝ) / (3 * (d : ℝ) ^ 2) ^ m := by
    rw [le_div_iff₀ (pow_pos ha m)]
    have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp _ ha.le m)
    calc
      _ ≤ Real.exp (-(3 * (d : ℝ) ^ 2)) *
          (Real.exp (3 * (d : ℝ) ^ 2) * (m.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]; simp
  have he' : Real.exp (-Real.pi * (d : ℝ) ^ 2) ≤
      (m.factorial : ℝ) / (3 * (d : ℝ) ^ 2) ^ m := by
    apply (Real.exp_le_exp.mpr _).trans he
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg (d : ℝ))]
  apply (correctionMoment_truncation n hz hdR).trans
  have h := div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left he' (by positivity : 0 ≤ 108 * (n.factorial : ℝ)))
    (by positivity : 0 < 3 * (d : ℝ)) (by nlinarith [Real.pi_gt_three] : 3 * (d : ℝ) ≤ Real.pi * d)
  apply h.trans_eq
  simp only [momentTailBudget, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_pow]
  ring

theorem sourceGaussianPhase_norm (eta : ℝ) (m : ℕ) : ‖sourceGaussianPhase eta m‖ = 1 := by
  unfold sourceGaussianPhase
  rw [norm_exp]
  simp [pow_two, mul_re, mul_im]

def r2HighMomentBudget (eta : ℝ) : ℝ :=
  5 / (16 * eta ^ 3) * (108 * (Nat.factorial 3 : ℝ)) +
  35 / (128 * eta ^ 4) * (108 * (Nat.factorial 4 : ℝ)) +
  (36 / (10 * eta ^ 3) + 63 / (256 * eta ^ 5)) * (108 * (Nat.factorial 5 : ℝ)) +
  (892 / (240 * eta ^ 4) + 231 / (1024 * eta ^ 6)) * (108 * (Nat.factorial 6 : ℝ))

theorem sourceLocalPolynomial_seven_high_moment_error {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    ‖-(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y) -
      sourceGaussianPhase eta m *
        ((rsPhi (sourcePhiParameter eta m) : ℂ) -
          (rsPhiOne (sourcePhiParameter eta m) : ℂ) / eta +
          ((rsPhiTwo (sourcePhiParameter eta m) : ℂ) +
            I / (96 * Real.pi) * (rsPhi (sourcePhiParameter eta m) : ℂ)) / (eta : ℂ) ^ 2)‖ ≤
      r2HighMomentBudget eta := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hz := sourcePhiParameter_mem h0.le h1.le
  have h3 := correctionMoment_bound 3 hz
  have h4 := correctionMoment_bound 4 hz
  have h5 := correctionMoment_bound 5 hz
  have h6 := correctionMoment_bound 6 hz
  let z := sourcePhiParameter eta m
  have hid : -(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y) -
      sourceGaussianPhase eta m *
        ((rsPhi z : ℂ) - (rsPhiOne z : ℂ) / eta +
          ((rsPhiTwo z : ℂ) + I / (96 * Real.pi) * (rsPhi z : ℂ)) / (eta : ℂ) ^ 2) =
      sourceGaussianPhase eta m *
        (-(5 / (16 * (eta : ℂ) ^ 3) * correctionMoment 3 z) +
          35 / (128 * (eta : ℂ) ^ 4) * correctionMoment 4 z +
          (9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) - 63 / (256 * (eta : ℂ) ^ 5)) *
            correctionMoment 5 z +
          (-(223 * Real.pi * I) / (240 * (eta : ℂ) ^ 4) + 231 / (1024 * (eta : ℂ) ^ 6)) *
            correctionMoment 6 z) := by
    rw [sourceLocalPolynomial_seven_phi h0 h1]
    dsimp [z]
    ring
  rw [hid, norm_mul, sourceGaussianPhase_norm, one_mul]
  unfold r2HighMomentBudget
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · apply (norm_add_le _ _).trans
      apply add_le_add
      · rw [norm_neg, norm_mul]
        simp only [norm_div, norm_mul, norm_pow, norm_ofNat, norm_real,
          Real.norm_eq_abs, abs_of_pos he]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      · rw [norm_mul]
        simp only [norm_div, norm_mul, norm_pow, norm_ofNat, norm_real,
          Real.norm_eq_abs, abs_of_pos he]
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    · rw [norm_mul]
      have hc : ‖9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) - 63 / (256 * (eta : ℂ) ^ 5)‖ ≤
          36 / (10 * eta ^ 3) + 63 / (256 * eta ^ 5) := by
        apply (norm_sub_le _ _).trans
        simp only [norm_div, norm_mul, norm_pow, norm_ofNat, norm_real, Real.norm_eq_abs,
          norm_I, mul_one, abs_of_pos he, abs_of_pos Real.pi_pos]
        gcongr
        linarith [Real.pi_lt_four]
      exact mul_le_mul hc h5 (norm_nonneg _) (by positivity)
  · rw [norm_mul]
    have hc : ‖-(223 * Real.pi * I) / (240 * (eta : ℂ) ^ 4) + 231 / (1024 * (eta : ℂ) ^ 6)‖ ≤
        892 / (240 * eta ^ 4) + 231 / (1024 * eta ^ 6) := by
      apply (norm_add_le _ _).trans
      simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_ofNat, norm_real, Real.norm_eq_abs,
        norm_I, mul_one, abs_of_pos he, abs_of_pos Real.pi_pos]
      gcongr
      linarith [Real.pi_lt_four]
    exact mul_le_mul hc h6 (norm_nonneg _) (by positivity)

theorem r2HighMomentBudget_simplified {eta : ℝ} :
    r2HighMomentBudget eta =
      93717 / (2 * eta ^ 3) + 1158867 / (4 * eta ^ 4) +
        25515 / (8 * eta ^ 5) + 280665 / (16 * eta ^ 6) := by
  norm_num [r2HighMomentBudget]
  ring

theorem sourcePhi_enclosure (N : ℕ) (r d : ℚ) {eta : ℝ} {m : ℕ}
    (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) (hr : |(r : ℝ)| ≤ 1)
    (hd : |sourcePhiParameter eta m - r| ≤ (d : ℝ)) :
    (phiEnclosure N r d).Contains (rsPhi (sourcePhiParameter eta m)) :=
  phiEnclosure_correct N r d hr (sourcePhiParameter_mem h0 h1) hd

theorem sourcePhiOne_enclosure (N : ℕ) (r h d : ℚ) {eta : ℝ} {m : ℕ}
    (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) (hr : |(r : ℝ)| ≤ 1)
    (hh : 0 < h) (h6 : 6 * h ≤ 1) (hd : |sourcePhiParameter eta m - r| ≤ (d : ℝ)) :
    (phiOneEnclosure N r h d).Contains (rsPhiOne (sourcePhiParameter eta m)) :=
  phiOneEnclosure_correct N r h d hr hh h6 (sourcePhiParameter_mem h0 h1) hd

theorem sourcePhiTwo_enclosure (N : ℕ) (r h d : ℚ) {eta : ℝ} {m : ℕ}
    (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) (hr : |(r : ℝ)| ≤ 1)
    (hh : 0 < h) (h6 : 6 * h ≤ 1) (hd : |sourcePhiParameter eta m - r| ≤ (d : ℝ)) :
    (phiTwoEnclosure N r h d).Contains (rsPhiTwo (sourcePhiParameter eta m)) :=
  phiTwoEnclosure_correct N r h d hr hh h6 (sourcePhiParameter_mem h0 h1) hd

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
