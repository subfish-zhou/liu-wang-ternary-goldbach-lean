import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.GateGeometry

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def scaledSource24Weight (q s : ℝ) : ℝ :=
  s ^ (-(3 / 2 : ℝ)) *
    (s * Real.log s / Real.pi - 0.874 * s + 6.8423 * q * Real.log s + 15 * q)

theorem linear_height_jacobian {q s : ℝ} (hq : 0 < q) (hs : 0 < s) :
    (1 / q) * heightKernel (s / q) = Real.sqrt q * heightKernel s := by
  rw [heightKernel, heightKernel, Real.rpow_def_of_pos (div_pos hs hq),
    Real.log_div hs.ne' hq.ne', Real.rpow_def_of_pos hs, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hq, ← Real.exp_add]
  have hqinv : 1 / q = Real.exp (-Real.log q) := by
    rw [Real.exp_neg, Real.exp_log hq, one_div]
  rw [hqinv, ← Real.exp_add]
  congr 1
  ring

theorem source24_linear_identity {q s : ℝ} (hq : 0 < q) :
    q * source24Envelope q (s / q) =
      s * Real.log s / Real.pi - 0.874 * s + 6.8423 * q * Real.log s + 15 * q := by
  unfold source24Envelope
  rw [mul_div_cancel₀ _ hq.ne']
  field_simp

theorem scaledSource24Weight_le {q P s : ℝ}
    (hq : 1 ≤ q) (hqP : q ≤ P) (hs : 1 ≤ s) :
    scaledSource24Weight q s ≤ lowWeight P s := by
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hb := source24Envelope_scaled_le hq hqP hs
  rw [source24_linear_identity hq0] at hb
  rw [lowWeight_factor hs0]
  unfold scaledSource24Weight
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hs0.le _)
  simp only [div_eq_mul_inv] at hb ⊢
  nlinarith only [hb]

theorem source24_height_change {q phi H u v : ℝ}
    (hq : 0 < q) (hu : 0 < u) (huv : u ≤ v) :
    (∫ y in u..v, heightKernel y * (phi * source24Envelope q y) *
      Real.exp (-0.478 * H / Real.log (q * y))) =
    (phi / Real.sqrt q) * ∫ s in (q * u)..(q * v),
      scaledSource24Weight q s * Real.exp (-0.478 * H / Real.log s) := by
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => t / q) (1 / q) s :=
    (hasDerivAt_id s).div_const q
  have hc := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := q * u) (b := q * v) (f := fun s : ℝ => s / q)
    (f' := fun _ : ℝ => 1 / q)
    (g := fun y : ℝ => heightKernel y * (phi * source24Envelope q y) *
      Real.exp (-0.478 * H / Real.log (q * y)))
    (by fun_prop) (fun s _ => hd s) (fun _ _ => by positivity)
  have he (x : ℝ) : q * x / q = x := by field_simp
  rw [he u, he v] at hc
  rw [← hc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (mul_le_mul_of_nonneg_left huv hq.le)] at hs
  have hs0 : 0 < s := (mul_pos hq hu).trans_le hs.1
  dsimp only [Function.comp_def, smul_eq_mul]
  rw [mul_div_cancel₀ _ hq.ne']
  have hj := linear_height_jacobian hq hs0
  have hsq0 : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hq24 := source24_linear_identity (s := s) hq
  unfold scaledSource24Weight
  rw [show s ^ (-(3 / 2 : ℝ)) = heightKernel s by unfold heightKernel; norm_num]
  change _ = phi / Real.sqrt q * (heightKernel s *
    (s * Real.log s / Real.pi - 0.874 * s + 6.8423 * q * Real.log s + 15 * q) *
      Real.exp (-0.478 * H / Real.log s))
  rw [← hq24]
  calc
    _ = ((1 / q) * heightKernel (s / q)) * (phi * source24Envelope q (s / q)) *
        Real.exp (-0.478 * H / Real.log s) := by ring
    _ = _ := by rw [hj]; field_simp; rw [Real.sq_sqrt hq.le]; ring

theorem normalized_low_fee {q phi L b : ℝ}
    (hq : 0 < q) (hphi : phi ≠ 0) (hL : L ≠ 0) :
    (8 * Real.sqrt q / phi) * (b * (phi / Real.sqrt q) / L) = 8 * b / L := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  field_simp

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
