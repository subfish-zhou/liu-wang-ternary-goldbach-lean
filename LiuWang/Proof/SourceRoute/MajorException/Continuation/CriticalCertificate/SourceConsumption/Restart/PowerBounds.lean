import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.ConductorPayment

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

theorem root_lower {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n)
    (h : a^n ≤ x) : a ≤ x^(1/(n:ℝ)) := by
  apply (pow_le_pow_iff_left₀ ha (Real.rpow_nonneg hx _) hn.ne').mp
  rw [← Real.rpow_mul_natCast hx]
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [one_div, inv_mul_cancel₀ hn0, Real.rpow_one]
  exact h

theorem negative_power_upper {x a t : ℝ} (hx : 0 ≤ x) (ha : 0 < a)
    (h : a ≤ x^t) : x^(-t) ≤ 1/a := by
  rw [Real.rpow_neg hx]
  simpa only [one_div] using one_div_le_one_div_of_le ha h

theorem conductor_negative_powers {r : ℝ} (hr : 987 ≤ r) :
    r^(-5/6:ℝ) ≤ 1/30 ∧ r^(-2/3:ℝ) ≤ 1 ∧ r^(-1/3:ℝ) ≤ 1/9 := by
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have h30 := root_lower hr0 (by norm_num : (0:ℝ)≤30)
    (by norm_num : 0<(2:ℕ)) (by nlinarith : (30:ℝ)^2≤r)
  have h9 := root_lower hr0 (by norm_num : (0:ℝ)≤9)
    (by norm_num : 0<(3:ℕ)) (by nlinarith : (9:ℝ)^3≤r)
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num : (-5/6:ℝ)≤ -(1/2))).trans
      (negative_power_upper hr0 (by norm_num) h30)
  constructor
  · simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num : (-2/3:ℝ)≤0)
  · simpa only [Nat.cast_ofNat, neg_div] using negative_power_upper hr0 (by norm_num) h9

theorem logarithmic_negative_powers {L : ℝ} (hL : 3100 ≤ L) :
    L^(-5/2:ℝ) ≤ 1/(3100^2*55:ℝ) ∧
    L^(-2:ℝ) ≤ 1/(3100^2:ℝ) ∧
    L^(-7/4:ℝ) ≤ 1/(3100*400:ℝ) := by
  have hL0 : 0 < L := by linarith
  have h55 : 55 ≤ L^(1/2:ℝ) :=
    root_lower hL0.le (by norm_num) (by norm_num : 0<(2:ℕ)) (by nlinarith)
  have h400 : 400 ≤ L^(3/4:ℝ) := by
    have h := root_lower (pow_nonneg hL0.le 3) (by norm_num : (0:ℝ)≤400)
      (by norm_num : 0<(4:ℕ))
      ((by norm_num : (400:ℝ)^4 ≤ 3100^3).trans
        (pow_le_pow_left₀ (by norm_num) hL 3))
    rw [← Real.rpow_natCast_mul hL0.le] at h
    norm_num at h ⊢
    exact h
  constructor
  · rw [show (-5/2:ℝ) = -(5/2) by ring]
    apply negative_power_upper hL0.le (by norm_num)
    rw [show (5/2:ℝ) = 2+1/2 by norm_num, Real.rpow_add hL0, Real.rpow_two]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hL 2) h55 (by norm_num) (by positivity)
  constructor
  · apply negative_power_upper hL0.le (by norm_num)
    simpa only [Real.rpow_two] using pow_le_pow_left₀ (by norm_num) hL 2
  · rw [show (-7/4:ℝ) = -(7/4) by ring]
    apply negative_power_upper hL0.le (by norm_num)
    rw [show (7/4:ℝ) = 1+3/4 by norm_num, Real.rpow_add hL0, Real.rpow_one]
    exact mul_le_mul hL h400 (by norm_num) hL0.le

theorem conductor_ratio_high {r : ℕ} {L : ℝ} (hr : 0 < r) (hL : 3100 ≤ L)
    (hrL : (r:ℝ) ≤ L^3) :
    ((r:ℝ)/(r.totient:ℝ))^2*L^(-5/2:ℝ) ≤ 7/(3100*400:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hq := totient_ratio_quarter hr
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg r) hrL (by norm_num : (0:ℝ)≤1/4)
  rw [← Real.rpow_natCast_mul hL0.le] at hpow
  norm_num only [show (3:ℝ)*(1/4)=3/4 by norm_num] at hpow
  calc
    _ ≤ (7*L^(3/4:ℝ))*L^(-5/2:ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (hq.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))) (by positivity)
    _ = 7*L^(-7/4:ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hL0]
      norm_num
    _ ≤ _ := (mul_le_mul_of_nonneg_left (logarithmic_negative_powers hL).2.2
      (by norm_num : (0:ℝ)≤7)).trans_eq (by ring)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
