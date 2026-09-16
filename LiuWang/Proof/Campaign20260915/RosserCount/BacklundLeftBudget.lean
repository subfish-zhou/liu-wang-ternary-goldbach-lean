import LiuWang.Proof.Campaign20260915.RosserCount.BacklundLeftIntegral
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_phase_cos_sin {q : ℚ} (hq : |q / 128| ≤ 1) :
    |Real.cos (q : ℝ) - ((unitRepeatedSquare 7 (q / 128)).1 : ℝ)| ≤
        (4 * 3 ^ 7 - 1) / 100000000 ∧
    |Real.sin (q : ℝ) - ((unitRepeatedSquare 7 (q / 128)).2 : ℝ)| ≤
        (4 * 3 ^ 7 - 1) / 100000000 := by
  have h := unitRepeatedSquare_error hq (by norm_num : (7 : ℕ) ≤ 7)
  rw [show (2 : ℝ) ^ 7 = 128 by norm_num] at h
  have he : (128 : ℝ) * ((q / 128 : ℚ) : ℝ) = (q : ℝ) := by push_cast; ring
  rw [he] at h
  have hr := (abs_re_le_norm
    (Complex.exp ((q : ℝ) * I) - (unitRepeatedSquare 7 (q / 128)).toComplex)).trans h
  have hi := (abs_im_le_norm
    (Complex.exp ((q : ℝ) * I) - (unitRepeatedSquare 7 (q / 128)).toComplex)).trans h
  have hexp : Complex.exp ((q : ℝ) * I) =
      (Real.cos (q : ℝ) : ℂ) + (Real.sin (q : ℝ) : ℂ) * I := by
    rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simpa only [hexp, QComplex.toComplex, sub_re, sub_im, add_re, add_im, mul_re, mul_im,
    ratCast_re, ratCast_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    mul_one, zero_add, add_zero, sub_zero] using And.intro hr hi

theorem backlund_left_cutoff_one :
    18955403 / 100000000 ≤ Real.cos (69 / 50 : ℝ) ∧
    Real.cos (69 / 50 : ℝ) ≤ 18972897 / 100000000 ∧
    Real.sin (69 / 50 : ℝ) ≤ 98194001 / 100000000 := by
  have h := backlund_phase_cos_sin (q := 69 / 50) (by norm_num)
  norm_num [unitRepeatedSquare, roundQComplex, squareQComplex, unitTaylor,
    roundRational, realIPower, imagIPower, Finset.sum_range_succ] at h
  obtain ⟨hc, hs⟩ := h
  rcases abs_le.mp hc with ⟨hcl, hcu⟩
  have hsu := (abs_le.mp hs).2
  constructor
  · linarith
  · constructor <;> linarith

theorem backlund_left_cutoff_two :
    94724253 / 100000000 ≤ Real.cos (163 / 500 : ℝ) ∧
    Real.cos (163 / 500 : ℝ) ≤ 94741747 / 100000000 ∧
    Real.sin (163 / 500 : ℝ) ≤ 4004281 / 12500000 := by
  have h := backlund_phase_cos_sin (q := 163 / 500) (by norm_num)
  norm_num [unitRepeatedSquare, roundQComplex, squareQComplex, unitTaylor,
    roundRational, realIPower, imagIPower, Finset.sum_range_succ] at h
  obtain ⟨hc, hs⟩ := h
  rcases abs_le.mp hc with ⟨hcl, hcu⟩
  have hsu := (abs_le.mp hs).2
  constructor
  · linarith
  · constructor <;> linarith

theorem backlund_left_coefficient_budget :
    (∫ θ in Real.pi / 2..Real.pi, backlundLeftCoefficient θ) ≤
      Real.pi * (77 / 500) := by
  have hp : Real.pi ≤ 355 / 113 := by linarith [Real.pi_lt_d20]
  have hp' : 3141592653589793238 / 1000000000000000000 ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have h1 := backlund_left_cutoff_one
  have h2 := backlund_left_cutoff_two
  have hδ1 : 0 ≤ (33 / 25 : ℝ) * Real.cos (69 / 50) - 1 / 4 := by linarith [h1.1]
  have hδ2 : 0 ≤ (33 / 25 : ℝ) * Real.cos (163 / 500) - 5 / 4 := by linarith [h2.1]
  have hi1 := backlund_cos_positive_integral_bound (by norm_num : (0 : ℝ) ≤ 33 / 25)
    (c := 69 / 50) ⟨by norm_num, by linarith⟩ hδ1
  have hi2 := backlund_cos_positive_integral_bound (by norm_num : (0 : ℝ) ≤ 33 / 25)
    (c := 163 / 500) ⟨by norm_num, by linarith⟩ hδ2
  have hm1 := mul_le_mul
    (show Real.pi / 2 - 69 / 50 ≤ 355 / 226 - (69 / 50 : ℝ) by linarith)
    (show (33 / 25 : ℝ) * Real.cos (69 / 50) - 1 / 4 ≤
      (33 / 25 : ℝ) * (18972897 / 100000000) - 1 / 4 by linarith [h1.2.1])
    hδ1 (by norm_num : (0 : ℝ) ≤ 355 / 226 - 69 / 50)
  have hm2 := mul_le_mul
    (show Real.pi / 2 - 163 / 500 ≤ 355 / 226 - (163 / 500 : ℝ) by linarith)
    (show (33 / 25 : ℝ) * Real.cos (163 / 500) - 5 / 4 ≤
      (33 / 25 : ℝ) * (94741747 / 100000000) - 5 / 4 by linarith [h2.2.1])
    hδ2 (by norm_num : (0 : ℝ) ≤ 355 / 226 - 163 / 500)
  rw [backlund_left_coefficient_reflect]
  nlinarith [h1.2.2, h2.2.2]

#print axioms backlund_phase_cos_sin
#print axioms backlund_left_cutoff_one
#print axioms backlund_left_cutoff_two
#print axioms backlund_left_coefficient_budget

end LiuWang.Proof.Campaign20260915.RosserCount
