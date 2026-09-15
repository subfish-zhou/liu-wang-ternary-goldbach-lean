import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityLogs

/-! A fixed AM-GM certificate for the all-domain high-beta density payment. -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem density_amgm {L s : ℝ} (hL : 3100 ≤ L) (hs : 0 < s) :
    48.2 * Real.sqrt (L / 3100) ≤ (251 / 640 : ℝ) * s + 0.478 * L / s := by
  have hsq := Real.sq_sqrt (show 0 ≤ L / 3100 by positivity)
  have ha := sq_nonneg ((251 / 640 : ℝ) * s - 24.1 * Real.sqrt (L / 3100))
  have hr := sq_nonneg (Real.sqrt (L / 3100))
  rw [show (251 / 640 : ℝ) * s + 0.478 * L / s =
    ((251 / 640 : ℝ) * s ^ 2 + 0.478 * L) / s by field_simp]
  apply (le_div_iff₀ hs).mpr
  nlinarith

theorem sixth_power_tangent {s : ℝ} (hs : 0 ≤ s) :
    s ^ 6 ≤ (60 : ℝ) ^ 6 * Real.exp (s / 10 - 6) := by
  have h := Real.add_one_le_exp (s / 60 - 1)
  have ht : s / 60 ≤ Real.exp (s / 60 - 1) := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ s / 60) ht 6
  rw [div_pow, ← Real.exp_nat_mul] at hp
  have he : Real.exp ((6 : ℕ) * (s / 60 - 1)) = Real.exp (s / 10 - 6) := by
    congr 1
    norm_num
    ring
  rw [he] at hp
  simpa only [mul_comm] using
    (div_le_iff₀ (by norm_num : (0 : ℝ) < 60 ^ 6)).mp hp

theorem density_sqrt_decay {L : ℝ} (hL : 3100 ≤ L) :
    L * Real.exp ((-9 / 10 : ℝ) - 48.2 * Real.sqrt (L / 3100)) ≤
      3100 * Real.exp (-49.1) := by
  let r := Real.sqrt (L / 3100)
  have hr : 1 ≤ r := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ L / 3100 by linarith)
    simpa only [Real.sqrt_one] using h
  have he : r ≤ Real.exp (r - 1) := by linarith [Real.add_one_le_exp (r - 1)]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ r) he 2
  have hl : L = 3100 * r ^ 2 := by
    have h := Real.sq_sqrt (show 0 ≤ L / 3100 by positivity)
    change r ^ 2 = L / 3100 at h
    linarith
  calc
    _ = 3100 * r ^ 2 * Real.exp (-9 / 10 - 48.2 * r) :=
      congrArg (fun t => t * Real.exp (-9 / 10 - 48.2 * r)) hl
    _ ≤ 3100 * Real.exp (r - 1) ^ 2 * Real.exp (-9 / 10 - 48.2 * r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (Real.exp_pos _).le
    _ = 3100 * Real.exp (2 * (r - 1) + (-9 / 10 - 48.2 * r)) := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem density_coupled_decay {L : ℝ} (hL : 3100 ≤ L) {q : ℕ} (hq : 0 < q)
    (hs : 0 < Real.log ((q : ℝ) * lowHeight)) :
    L * (Real.sqrt q / q.totient) * Real.log ((q : ℝ) * lowHeight) ^ 6 *
        Real.exp (-0.478 * L / Real.log ((q : ℝ) * lowHeight)) ≤
      6 * 60 ^ 6 * 3100 * Real.exp (-49.1) := by
  let s := Real.log ((q : ℝ) * lowHeight)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hid : s = Real.log q + Real.log lowHeight :=
    Real.log_mul hqR.ne' lowHeight_pos.ne'
  have ha := density_amgm (s := s) hL hs
  have hb : -(63 / 128 : ℝ) * Real.log q + (s / 10 - 6) -
      0.478 * L / s ≤ -9 / 10 - 48.2 * Real.sqrt (L / 3100) := by
    rw [hid] at ha ⊢
    linarith [lowHeight_log_bounds.2]
  have hp := mul_le_mul (totient_coupled_decay hq) (sixth_power_tangent hs.le)
    (pow_nonneg hs.le 6) (by positivity)
  have hp := mul_le_mul_of_nonneg_left hp (show 0 ≤ L by linarith)
  have hp := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-0.478 * L / s)).le
  calc
    _ ≤ L * (6 * Real.exp (-(63 / 128 : ℝ) * Real.log q) *
        (60 ^ 6 * Real.exp (s / 10 - 6))) * Real.exp (-0.478 * L / s) := by
      simpa only [mul_assoc] using hp
    _ = (6 * 60 ^ 6) * (L * Real.exp (-(63 / 128 : ℝ) * Real.log q +
        (s / 10 - 6) - 0.478 * L / s)) := by
      rw [show -(63 / 128 : ℝ) * Real.log q + (s / 10 - 6) - 0.478 * L / s =
        -(63 / 128 : ℝ) * Real.log q + (s / 10 - 6) + (-0.478 * L / s) by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ (6 * 60 ^ 6) * (L * Real.exp (-9 / 10 - 48.2 * Real.sqrt (L / 3100))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by linarith)) (by norm_num)
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (density_sqrt_decay hL)
        (by norm_num : (0 : ℝ) ≤ 6 * 60 ^ 6)

theorem density_endpoint_certificate :
    ((60 / 59) * (10 / 9) * (16541 + 9 * 24200) * (11 / 10) ^ 6 *
      (6 * 60 ^ 6 * 3100) : ℝ) * Real.exp (-49.1) ≤ 0.24981 := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.71)
    (by linarith [Real.exp_one_gt_d9] : (2.71 : ℝ) ≤ Real.exp 1) 49
  rw [← Real.exp_nat_mul] at he
  simp only [Nat.cast_ofNat, mul_one] at he
  have hh : (1.1 : ℝ) ≤ Real.exp 0.1 := by linarith [Real.add_one_le_exp 0.1]
  have hp := mul_le_mul he hh (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at hp
  rw [show (49 : ℝ) + 0.1 = 49.1 by norm_num] at hp
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  exact (by norm_num :
    ((60 / 59) * (10 / 9) * (16541 + 9 * 24200) * (11 / 10) ^ 6 *
      (6 * 60 ^ 6 * 3100) : ℝ) ≤ 0.24981 * (2.71 ^ 49 * 1.1)).trans
      (mul_le_mul_of_nonneg_left hp (by norm_num))

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
