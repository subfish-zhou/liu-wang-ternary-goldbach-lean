import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryActual

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def source24Envelope (r y : ℝ) : ℝ :=
  y / Real.pi * Real.log (r * y) - 0.874 * y + 6.8423 * Real.log (r * y) + 15

def lowWeight (P y : ℝ) : ℝ :=
  y ^ (-(1 / 2 : ℝ)) * Real.log (P * y) / Real.pi -
    0.874 * y ^ (-(1 / 2 : ℝ)) +
    6.8423 * P * y ^ (-(3 / 2 : ℝ)) * Real.log (P * y) +
    15 * P * y ^ (-(3 / 2 : ℝ))

def originalLowScalar (L : ℝ) : ℝ :=
  ∫ y in (3.36 * L ^ (3 : ℕ))..(10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ))),
    L * lowWeight (L ^ (3 : ℕ)) y *
      Real.exp (-0.478 * (L + Real.log 0.001) / Real.log y)

theorem source24Envelope_mono_real_modulus {r P y : ℝ}
    (hr : 0 < r) (hrP : r ≤ P) (hy : 0 ≤ y) :
    source24Envelope r y ≤ source24Envelope P y := by
  by_cases hy0 : y = 0
  · simp [hy0, source24Envelope]
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hl := Real.log_le_log (mul_pos hr hyp) (mul_le_mul_of_nonneg_right hrP hy)
  unfold source24Envelope
  have h1 := mul_le_mul_of_nonneg_left hl (div_nonneg hy Real.pi_pos.le)
  linarith

theorem source24Envelope_nonneg {r y : ℝ}
    (hy : 3.36 ≤ y) (hz : 3 ≤ Real.log (r * y)) :
    0 ≤ source24Envelope r y := by
  have hy0 : 0 < y := by linarith
  have hc : (0.874 : ℝ) ≤ Real.log (r * y) / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_d2]
  have hm := mul_nonneg (sub_nonneg.mpr hc) hy0.le
  unfold source24Envelope
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm, hz]

theorem lowWeight_factor {P y : ℝ} (hy : 0 < y) :
    lowWeight P y =
      y ^ (-(3 / 2 : ℝ)) *
        (y * (Real.log (P * y) / Real.pi - 0.874) +
          P * (6.8423 * Real.log (P * y) + 15)) := by
  have he : y ^ (-(3 / 2 : ℝ)) * y = y ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = y ^ (-(3 / 2 : ℝ)) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hy]; norm_num
  unfold lowWeight
  calc
    _ = (y ^ (-(3 / 2 : ℝ)) * y) * Real.log (P * y) / Real.pi -
        0.874 * (y ^ (-(3 / 2 : ℝ)) * y) +
        6.8423 * P * y ^ (-(3 / 2 : ℝ)) * Real.log (P * y) +
        15 * P * y ^ (-(3 / 2 : ℝ)) := by rw [he]
    _ = _ := by ring

theorem lowWeight_nonneg {P y : ℝ}
    (hP : 0 ≤ P) (hy : 0 < y) (hz : 3 ≤ Real.log (P * y)) :
    0 ≤ lowWeight P y := by
  rw [lowWeight_factor hy]
  have hc : (0.874 : ℝ) ≤ Real.log (P * y) / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_d2]
  have ha : 0 ≤ Real.log (P * y) / Real.pi - 0.874 := sub_nonneg.mpr hc
  have hb : 0 ≤ 6.8423 * Real.log (P * y) + 15 := by linarith
  positivity

theorem source24Envelope_scaled_le {q P s : ℝ}
    (hq : 1 ≤ q) (hqP : q ≤ P) (hs : 1 ≤ s) :
    q * source24Envelope q (s / q) ≤
      s * Real.log (P * s) / Real.pi - 0.874 * s +
        6.8423 * P * Real.log (P * s) + 15 * P := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hP : 1 ≤ P := hq.trans hqP
  have hlog := Real.log_le_log hs0 (le_mul_of_one_le_left hs0.le hP)
  have hprod : q * Real.log s ≤ P * Real.log (P * s) :=
    mul_le_mul hqP hlog (Real.log_nonneg hs) (by linarith)
  have hmain := mul_le_mul_of_nonneg_left hlog (div_nonneg hs0.le Real.pi_pos.le)
  unfold source24Envelope
  rw [mul_div_cancel₀ _ hq0.ne']
  have he : q * (s / q / Real.pi * Real.log s - 0.874 * (s / q) +
      6.8423 * Real.log s + 15) =
      s / Real.pi * Real.log s - 0.874 * s +
        6.8423 * q * Real.log s + 15 * q := by field_simp
  rw [he]
  simp only [div_eq_mul_inv] at hmain ⊢
  nlinarith only [hprod, hmain, hqP]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
