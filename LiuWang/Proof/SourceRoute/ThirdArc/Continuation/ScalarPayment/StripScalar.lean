import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.Totient
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.TableIntegrals

/-! Coupled-q analytic payment of the original (5.25) scalar. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment

theorem lowHeight_log_le_eleven : Real.log lowHeight ≤ 11 := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
    (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1) 11
  rw [← Real.exp_nat_mul] at he
  norm_num at he
  apply (Real.log_le_iff_le_exp lowHeight_pos).mpr
  unfold lowHeight
  nlinarith [Real.pi_lt_four]

theorem totient_constant_le_six : totientConstant ≤ (6 : ℝ) ^ 128 :=
  totient_endpoint_certificates.2.trans (by norm_num)

theorem totient_coupled_decay {q : ℕ} (hq : 0 < q) :
    Real.sqrt q / q.totient ≤ 6 * Real.exp (-(63 / 128 : ℝ) * Real.log q) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hs : (Real.sqrt (q : ℝ)) ^ 128 = (q : ℝ) ^ 64 := by
    rw [show (128 : ℕ) = 2 * 64 by norm_num, pow_mul, Real.sq_sqrt hqR.le]
  have he : Real.exp ((63 / 128 : ℝ) * Real.log q) ^ 128 = (q : ℝ) ^ 63 := by
    rw [← Real.exp_nat_mul]
    calc
      _ = Real.exp ((63 : ℕ) * Real.log q) := by congr 1; norm_num; ring
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hqR]
  have hp : (Real.sqrt q / q.totient * Real.exp ((63 / 128 : ℝ) * Real.log q)) ^ 128 ≤
      (6 : ℝ) ^ 128 := by
    rw [mul_pow, div_pow, hs, he, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos hf 128)).mpr
    have h := (totient_power_bound hq).trans
      (mul_le_mul_of_nonneg_right totient_constant_le_six (pow_nonneg hf.le 128))
    convert h using 1
    ring
  have hp := (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : 128 ≠ 0)).mp hp
  apply le_of_mul_le_mul_right (a := Real.exp ((63 / 128 : ℝ) * Real.log q)) ?_
    (Real.exp_pos _)
  calc
    _ ≤ 6 := hp
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf; simp

theorem coupled_amgm {L s : ℝ} (hL : 3100 ≤ L) (hs : 0 < s) :
    (71 / 2 : ℝ) * Real.sqrt (L / 3100) ≤ (63 / 128 : ℝ) * s + 0.2067 * L / s := by
  have hsq := Real.sq_sqrt (show 0 ≤ L / 3100 by positivity)
  have hLr : L = 3100 * Real.sqrt (L / 3100) ^ 2 := by nlinarith
  have ha := sq_nonneg ((63 / 128 : ℝ) * s - (71 / 4) * Real.sqrt (L / 3100))
  have hr := sq_nonneg (Real.sqrt (L / 3100))
  have hd : (63 / 128 : ℝ) * s + 0.2067 * L / s =
      ((63 / 128 : ℝ) * s ^ 2 + 0.2067 * L) / s := by field_simp
  rw [hd]
  apply (le_div_iff₀ hs).mpr
  nlinarith

theorem sqrt_exponential_decay {L : ℝ} (hL : 3100 ≤ L) :
    L * Real.exp ((11 / 2 : ℝ) - (71 / 2) * Real.sqrt (L / 3100)) ≤
      3100 * Real.exp (-30) := by
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
    _ = 3100 * r ^ 2 * Real.exp (11 / 2 - (71 / 2) * r) :=
      congrArg (fun t => t * Real.exp (11 / 2 - (71 / 2) * r)) hl
    _ ≤ 3100 * Real.exp (r - 1) ^ 2 * Real.exp (11 / 2 - (71 / 2) * r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (Real.exp_pos _).le
    _ = 3100 * Real.exp (2 * (r - 1) + (11 / 2 - (71 / 2) * r)) := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem low_strip_coupled_decay {L : ℝ} (hL : 3100 ≤ L) {q : ℕ} (hq : 0 < q)
    (hs : 0 < Real.log ((q : ℝ) * lowHeight)) :
    L * (Real.sqrt q / q.totient) *
        Real.exp (-0.2067 * L / Real.log ((q : ℝ) * lowHeight)) ≤
      6 * 3100 * Real.exp (-30) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hid : Real.log ((q : ℝ) * lowHeight) = Real.log q + Real.log lowHeight :=
    Real.log_mul hqR.ne' lowHeight_pos.ne'
  have ha := coupled_amgm hL hs
  have hb : -(63 / 128 : ℝ) * Real.log q -
      0.2067 * L / Real.log ((q : ℝ) * lowHeight) ≤
        11 / 2 - (71 / 2) * Real.sqrt (L / 3100) := by
    rw [hid] at ha ⊢
    linarith [lowHeight_log_le_eleven]
  calc
    _ ≤ L * (6 * Real.exp (-(63 / 128 : ℝ) * Real.log q)) *
        Real.exp (-0.2067 * L / Real.log ((q : ℝ) * lowHeight)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (totient_coupled_decay hq) (by linarith)) (Real.exp_pos _).le
    _ = 6 * (L * Real.exp (-(63 / 128 : ℝ) * Real.log q -
        0.2067 * L / Real.log ((q : ℝ) * lowHeight))) := by
      rw [show -0.2067 * L / Real.log ((q : ℝ) * lowHeight) =
        -(0.2067 * L / Real.log ((q : ℝ) * lowHeight)) by ring,
        Real.exp_neg, Real.exp_sub]
      ring
    _ ≤ 6 * (L * Real.exp (11 / 2 - (71 / 2) * Real.sqrt (L / 3100))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by linarith)) (by norm_num)
    _ ≤ _ := by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (sqrt_exponential_decay hL) (by norm_num : (0 : ℝ) ≤ 6)

theorem strip_endpoint_certificate :
    (14000 * (60 / 59) * 6 * 3100 : ℝ) * Real.exp (-30) ≤ 0.00003 := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.71)
    (by linarith [Real.exp_one_gt_d9] : (2.71 : ℝ) ≤ Real.exp 1) 30
  rw [← Real.exp_nat_mul] at he
  simp only [Nat.cast_ofNat, mul_one] at he
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  exact (by norm_num : (14000 * (60 / 59) * 6 * 3100 : ℝ) ≤ 0.00003 * 2.71 ^ 30).trans
    (mul_le_mul_of_nonneg_left he (by norm_num))

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment
