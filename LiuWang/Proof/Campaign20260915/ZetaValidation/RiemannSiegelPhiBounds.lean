import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelPhi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rs_sinc_lower {x : ℝ} (hx : |x| ≤ 3 * Real.pi / 4) :
    1 / 6 ≤ Real.sinc x := by
  have hpos (y : ℝ) (hy : 0 < y) (hb : y ≤ 3 * Real.pi / 4) :
      1 / 6 ≤ Real.sinc y := by
    rw [Real.sinc_of_ne_zero hy.ne', le_div_iff₀ hy]
    have hpi := Real.pi_lt_four
    by_cases hh : y ≤ Real.pi / 2
    · have hs := Real.mul_le_sin hy.le hh
      have hc : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]
        linarith
      nlinarith
    · have hs := Real.mul_le_sin (x := Real.pi - y) (by linarith) (by linarith)
      rw [Real.sin_pi_sub] at hs
      have hc : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]
        linarith
      have hd : y / 3 ≤ Real.pi - y := by linarith
      nlinarith
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · rw [← Real.sinc_neg]
    exact hpos (-x) (neg_pos.mpr hn) (by rwa [abs_of_neg hn] at hx)
  · norm_num
  · exact hpos x hp (by rwa [abs_of_pos hp] at hx)

theorem rsPhi_denominator_lower {z : ℝ} (hz : |z| ≤ 1) :
    Real.pi / 36 ≤ Real.pi * (Real.sinc (Real.pi / 2 * (z + 1 / 2)) *
      Real.sinc (Real.pi / 2 * (z - 1 / 2))) := by
  have h := abs_le.mp hz
  have hp : |Real.pi / 2 * (z + 1 / 2)| ≤ 3 * Real.pi / 4 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.pi_pos]
  have hm : |Real.pi / 2 * (z - 1 / 2)| ≤ 3 * Real.pi / 4 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.pi_pos]
  have hl := mul_le_mul (rs_sinc_lower hp) (rs_sinc_lower hm)
    (by norm_num : (0 : ℝ) ≤ 1 / 6) (by linarith [rs_sinc_lower hp])
  nlinarith [mul_le_mul_of_nonneg_left hl Real.pi_pos.le]

theorem rsPhi_uniform_bound {z : ℝ} (hz : |z| ≤ 1) :
    0 < rsPhi z ∧ rsPhi z ≤ 12 := by
  have hd := rsPhi_denominator_lower hz
  have hp := rsPhi_denominator_pos (by linarith : |z| < 3 / 2)
  have hz2 : z ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one z).mpr hz
  have hn : |Real.pi / 2 * (z ^ 2 - 1 / 4)| < Real.pi := by
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg z, Real.pi_pos]
  constructor
  · exact div_pos (rs_sinc_pos hn) hp
  · unfold rsPhi
    rw [div_le_iff₀ hp]
    have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    linarith [Real.sinc_le_one (Real.pi / 2 * (z ^ 2 - 1 / 4))]

def rsPhiOne (z : ℝ) : ℝ := iteratedDeriv 3 rsPhi z / (12 * Real.pi ^ 2)

def rsPhiTwo (z : ℝ) : ℝ :=
  iteratedDeriv 2 rsPhi z / (16 * Real.pi ^ 2) +
    iteratedDeriv 6 rsPhi z / (288 * Real.pi ^ 4)

theorem rsPhiOne_analytic {z : ℝ} (hz : |z| < 3 / 2) : AnalyticAt ℝ rsPhiOne z := by
  unfold rsPhiOne
  simp_rw [iteratedDeriv_eq_iterate]
  exact (rsPhi_iterated_deriv_analytic hz 3).div_const

theorem rsPhiTwo_analytic {z : ℝ} (hz : |z| < 3 / 2) : AnalyticAt ℝ rsPhiTwo z := by
  unfold rsPhiTwo
  simp_rw [iteratedDeriv_eq_iterate]
  exact ((rsPhi_iterated_deriv_analytic hz 2).div_const (c := 16 * Real.pi ^ 2)).add
      ((rsPhi_iterated_deriv_analytic hz 6).div_const (c := 288 * Real.pi ^ 4))

theorem rsPhi_deriv_parity (n : ℕ) (z : ℝ) :
    iteratedDeriv n rsPhi (-z) = (-1 : ℝ) ^ n * iteratedDeriv n rsPhi z := by
  have he : (fun x => rsPhi (-x)) = rsPhi := funext rsPhi_even
  have h := iteratedDeriv_comp_neg n rsPhi z
  rw [he, smul_eq_mul] at h
  have hp : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * iteratedDeriv n rsPhi (-z) := by rw [hp, one_mul]
    _ = _ := by rw [mul_assoc, ← h]

theorem rsPhiOne_odd (z : ℝ) : rsPhiOne (-z) = -rsPhiOne z := by
  norm_num [rsPhiOne, rsPhi_deriv_parity]
  ring

theorem rsPhiTwo_even (z : ℝ) : rsPhiTwo (-z) = rsPhiTwo z := by
  norm_num [rsPhiTwo, rsPhi_deriv_parity]

end LiuWang.Proof.Campaign20260915.ZetaValidation
