import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.KernelBounds
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

def gaussianBudget : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => 4 * (n + 1) * gaussianBudget n

def derivativeBudget (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1),
    n.choose j * 8 ^ j * (108 * j.factorial) * gaussianBudget (n - j)

theorem gaussianJet_bound (n : ℕ) {c : ℂ} (hc : ‖c‖ ≤ 2) :
    ‖gaussianJet c n‖ ≤ (gaussianBudget n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gaussianJet_zero, gaussianBudget]
  | one => simp [gaussianJet_one, gaussianBudget]
  | more n hn _ =>
    rw [gaussianJet_rec, norm_mul, norm_mul]
    simp only [norm_mul, norm_ofNat, gaussianBudget,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    have he : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using norm_natCast (n + 1 : ℕ) (α := ℂ)
    rw [he]
    calc
      _ ≤ (2 * 2) * ((n : ℝ) + 1) * (gaussianBudget n : ℝ) := by gcongr
      _ = _ := by ring

theorem rsPhi_derivative_bound (n : ℕ) {z : ℝ} (hz : |z| ≤ 1) :
    |iteratedDeriv n rsPhi z| ≤ (derivativeBudget n : ℝ) := by
  have hc : ‖(-Real.pi * I / 2 : ℂ)‖ ≤ 2 := by
    simp only [norm_div, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, norm_I, norm_ofNat,
      abs_of_pos Real.pi_pos, mul_one]
    linarith [Real.pi_lt_four]
  have hq : 2 * Real.pi ≤ 8 := by
    linarith [Real.pi_lt_four]
  have he := correctionIntegral_deriv_moment_sum n (z : ℂ)
  rw [correctionIntegral_iteratedDeriv_eq_rsPhi n (by linarith : |z| < 3 / 2)] at he
  calc
    _ = ‖((iteratedDeriv n rsPhi z : ℝ) : ℂ)‖ := by simp
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        ‖(n.choose j : ℂ) * ((2 * Real.pi * I : ℂ) ^ j * correctionMoment j z) *
          gaussianJet (-Real.pi * I / 2) (n - j)‖ := by
      rw [he]
      exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * 8 ^ j * (108 * (j.factorial : ℝ)) *
          (gaussianBudget (n - j) : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_pow, Complex.norm_natCast, norm_ofNat, norm_real,
        Real.norm_eq_abs, norm_I, abs_of_pos Real.pi_pos, mul_one]
      have hm := correctionMoment_bound j hz
      have hg := gaussianJet_bound (n - j) hc
      calc
        _ ≤ (n.choose j : ℝ) * (8 ^ j * (108 * (j.factorial : ℝ))) *
            (gaussianBudget (n - j) : ℝ) := by gcongr
        _ = _ := by ring
    _ = _ := by simp [derivativeBudget]

theorem rsPhi_derivative_lipschitz (n : ℕ) {x y : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |iteratedDeriv n rsPhi x - iteratedDeriv n rsPhi y| ≤
      (derivativeBudget (n + 1) : ℝ) * |x - y| := by
  have hd : ∀ u ∈ Icc (-1 : ℝ) 1, DifferentiableAt ℝ (iteratedDeriv n rsPhi) u := by
    intro u hu
    have ha := rsPhi_iterated_deriv_analytic
      (z := u) (by rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]) n
    simpa only [iteratedDeriv_eq_iterate] using ha.differentiableAt
  have hb : ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖deriv (iteratedDeriv n rsPhi) u‖ ≤ (derivativeBudget (n + 1) : ℝ) := by
    intro u hu
    rw [← iteratedDeriv_succ, Real.norm_eq_abs]
    exact rsPhi_derivative_bound (n + 1) (abs_le.mpr hu)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc (-1 : ℝ) 1)
      (abs_le.mp hy) (abs_le.mp hx)

def phiOneBudget : ℚ := (derivativeBudget 3 : ℚ) / 108

def phiTwoBudget : ℚ :=
  (derivativeBudget 2 : ℚ) / 144 + (derivativeBudget 6 : ℚ) / 23328

def phiOneInputBudget : ℚ := (derivativeBudget 4 : ℚ) / 108

def phiTwoInputBudget : ℚ :=
  (derivativeBudget 3 : ℚ) / 144 + (derivativeBudget 7 : ℚ) / 23328

theorem pi_square_lower : (9 : ℝ) ≤ Real.pi ^ 2 := by
  nlinarith [Real.pi_gt_three]

theorem pi_fourth_lower : (81 : ℝ) ≤ Real.pi ^ 4 := by
  nlinarith [pi_square_lower, sq_nonneg (Real.pi ^ 2 - 9),
    show Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 by ring]

theorem rsPhiOne_bound {z : ℝ} (hz : |z| ≤ 1) :
    |rsPhiOne z| ≤ (phiOneBudget : ℝ) := by
  rw [rsPhiOne, abs_div, abs_of_pos (by positivity : 0 < 12 * Real.pi ^ 2)]
  simp only [phiOneBudget, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  exact div_le_div₀ (by positivity) (rsPhi_derivative_bound 3 hz)
    (by norm_num) (by nlinarith [pi_square_lower])

theorem rsPhiTwo_bound {z : ℝ} (hz : |z| ≤ 1) :
    |rsPhiTwo z| ≤ (phiTwoBudget : ℝ) := by
  unfold rsPhiTwo
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < 16 * Real.pi ^ 2),
    abs_of_pos (by positivity : 0 < 288 * Real.pi ^ 4)]
  simp only [phiTwoBudget, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  apply add_le_add
  · exact div_le_div₀ (by positivity) (rsPhi_derivative_bound 2 hz)
      (by norm_num) (by nlinarith [pi_square_lower])
  · exact div_le_div₀ (by positivity) (rsPhi_derivative_bound 6 hz)
      (by norm_num) (by nlinarith [pi_fourth_lower])

theorem rsPhiOne_lipschitz {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |rsPhiOne x - rsPhiOne y| ≤ (phiOneInputBudget : ℝ) * |x - y| := by
  rw [rsPhiOne, rsPhiOne, ← sub_div, abs_div,
    abs_of_pos (by positivity : 0 < 12 * Real.pi ^ 2)]
  have h := div_le_div₀ (by positivity) (rsPhi_derivative_lipschitz 3 hx hy)
    (by norm_num : (0 : ℝ) < 108) (by nlinarith [pi_square_lower] : 108 ≤ 12 * Real.pi ^ 2)
  apply h.trans_eq
  simp only [phiOneInputBudget, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  ring

theorem rsPhiTwo_lipschitz {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |rsPhiTwo x - rsPhiTwo y| ≤ (phiTwoInputBudget : ℝ) * |x - y| := by
  have he : rsPhiTwo x - rsPhiTwo y =
      (iteratedDeriv 2 rsPhi x - iteratedDeriv 2 rsPhi y) / (16 * Real.pi ^ 2) +
      (iteratedDeriv 6 rsPhi x - iteratedDeriv 6 rsPhi y) / (288 * Real.pi ^ 4) := by
    unfold rsPhiTwo
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < 16 * Real.pi ^ 2),
    abs_of_pos (by positivity : 0 < 288 * Real.pi ^ 4)]
  have h2 := div_le_div₀ (by positivity) (rsPhi_derivative_lipschitz 2 hx hy)
    (by norm_num : (0 : ℝ) < 144) (by nlinarith [pi_square_lower] : 144 ≤ 16 * Real.pi ^ 2)
  have h6 := div_le_div₀ (by positivity) (rsPhi_derivative_lipschitz 6 hx hy)
    (by norm_num : (0 : ℝ) < 23328)
    (by nlinarith [pi_fourth_lower] : 23328 ≤ 288 * Real.pi ^ 4)
  apply (add_le_add h2 h6).trans_eq
  simp only [phiTwoInputBudget, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  ring

theorem rsPhi_derivative_input_error (n : ℕ) {x y q e d : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hq : |iteratedDeriv n rsPhi y - q| ≤ e) (hd : |x - y| ≤ d) :
    |iteratedDeriv n rsPhi x - q| ≤ e + (derivativeBudget (n + 1) : ℝ) * d := by
  have h := abs_sub_le (iteratedDeriv n rsPhi x) (iteratedDeriv n rsPhi y) q
  have h' := (rsPhi_derivative_lipschitz n hx hy).trans
    (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _))
  linarith

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
