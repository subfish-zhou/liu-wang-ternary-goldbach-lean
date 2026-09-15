import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Payment
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Coefficients

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526

def originalScalar (K d L x : ℝ) : ℝ :=
  K * lowCoefficient (59 / 60) * L ^ (1 - x / 2) * sourceNu (L ^ x) *
    Real.exp (-d * L / Real.log (10000 * Real.pi * L ^ x))

def scalar525 (L x : ℝ) : ℝ := originalScalar 14000 0.2067 L x

def scalar526 (L x : ℝ) : ℝ := originalScalar 2 0.10367089 L x

def logScalar (K d L s : ℝ) : ℝ :=
  K * lowCoefficient (59 / 60) * L * Source524.logNu s *
    Real.exp (-(1 / 2 : ℝ) * s) *
      Real.exp (-d * L / (s + Real.log lowHeight))

theorem originalScalar_eq_logScalar {L x : ℝ} (hL : 0 < L) (K d : ℝ) :
    originalScalar K d L x = logScalar K d L (x * Real.log L) := by
  have hp : Real.log (10000 * Real.pi * L ^ x) =
      x * Real.log L + Real.log lowHeight := by
    rw [Real.log_mul (by positivity : (10000 * Real.pi : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hL x).ne', Real.log_rpow hL]
    unfold lowHeight
    ring
  have he : L ^ (1 - x / 2) = L * Real.exp (-(1 / 2 : ℝ) * (x * Real.log L)) := by
    rw [Real.rpow_def_of_pos hL, show Real.log L * (1 - x / 2) =
      Real.log L + (-(1 / 2 : ℝ) * (x * Real.log L)) by ring,
      Real.exp_add, Real.exp_log hL]
  unfold originalScalar logScalar
  rw [hp, he]
  simp only [sourceNu, Source524.logNu, Real.log_rpow hL]
  ring

theorem original_exponential_scaling {L x d : ℝ} (hL : 3100 ≤ L)
    (hx : 3 ≤ x) (hx1 : x ≤ 6) (hd : 0.10367089 ≤ d) (hd1 : d ≤ 0.2067) :
    Real.exp (-d * L / (x * Real.log L + Real.log lowHeight)) ≤
      Real.exp (-d * 3100 / (x * Real.log 3100 + Real.log lowHeight)) /
        (L / 3100) ^ (2 : ℕ) := by
  let z := Real.log (L / 3100)
  let t₀ := x * Real.log 3100 + Real.log lowHeight
  let t := x * Real.log L + Real.log lowHeight
  let A := d * 3100 / t₀
  have hL0 : 0 < L := by linarith
  have hz : 0 ≤ z := Real.log_nonneg (by linarith)
  have he : Real.exp z = L / 3100 := Real.exp_log (by positivity)
  have ht₀ : 34 ≤ t₀ ∧ t₀ ≤ 59 := by
    have h := Source524.real_parameter_scaling hL hx hx1
    dsimp only [t₀]
    constructor <;> linarith [h.1, h.2.1, lowHeight_log_bounds.1, lowHeight_log_bounds.2]
  have ht₀0 : 0 < t₀ := by linarith [ht₀.1]
  have hid : t = t₀ + x * z := by
    dsimp only [t, t₀, z]
    rw [Real.log_div hL0.ne' (by norm_num)]
    ring
  have ht0 : 0 < t := by rw [hid]; nlinarith
  have ht : t ≤ t₀ + 6 * z := by rw [hid]; nlinarith
  have hA : 0 ≤ A := div_nonneg (by linarith) ht₀0.le
  have hAup : A ≤ 19 := by
    apply (div_le_iff₀ ht₀0).mpr
    linarith [ht₀.1]
  have hAt : A * t₀ = d * 3100 := div_mul_cancel₀ _ ht₀0.ne'
  have hquad := Real.quadratic_le_exp_of_nonneg hz
  rw [he] at hquad
  have hp := mul_le_mul_of_nonneg_left ht (show 0 ≤ A + 2 * z by positivity)
  have hAz := mul_le_mul_of_nonneg_right hAup hz
  have htz := mul_le_mul_of_nonneg_right ht₀.2 hz
  have hq := mul_le_mul_of_nonneg_left hquad (show 0 ≤ d * 3100 by linarith)
  have hdz := mul_le_mul_of_nonneg_right hd hz
  have hdz2 := mul_le_mul_of_nonneg_right hd (sq_nonneg z)
  have hgap : (A + 2 * z) * t ≤ d * L := by
    nlinarith only [hp, hAz, htz, hAt, hq, hdz, hdz2, hz, sq_nonneg z]
  have hdiv : A + 2 * z ≤ d * L / t := (le_div_iff₀ ht0).mpr hgap
  calc
    _ ≤ Real.exp (-A - 2 * z) := Real.exp_le_exp.mpr (by
      change -d * L / t ≤ -A - 2 * z
      rw [neg_mul, neg_div]
      linarith)
    _ = _ := by
      rw [Real.exp_sub, show (2 : ℝ) * z = (2 : ℕ) * z by norm_num,
        Real.exp_nat_mul, he]
      congr 1
      congr 1
      dsimp only [A, t₀]
      ring

theorem originalScalar_reduce_L {K d L x : ℝ} (hK : 0 ≤ K) (hL : 3100 ≤ L)
    (hx : 3 ≤ x) (hx1 : x ≤ 6) (hd : 0.10367089 ≤ d) (hd1 : d ≤ 0.2067) :
    originalScalar K d L x ≤ originalScalar K d 3100 x := by
  have hs := Source524.real_parameter_scaling hL hx hx1
  have hr : 1 ≤ L / 3100 := by linarith
  have hn := Source524.logNu_scaling hs.1 hr hs.2.2.1 hs.2.2.2
  have hn0 := (Source524.logNu_bounds (hs.1.trans hs.2.2.1)).2
  have hn₀0 := (Source524.logNu_bounds hs.1).2
  have he := Real.exp_le_exp.mpr (show -(1 / 2 : ℝ) * (x * Real.log L) ≤
    -(1 / 2 : ℝ) * (x * Real.log 3100) by linarith [hs.2.2.1])
  have hc := lowCoefficient_nonneg (by norm_num : (0 : ℝ) < 59 / 60)
  have h := mul_le_mul (mul_le_mul hn he (Real.exp_pos _).le (by positivity))
    (original_exponential_scaling hL hx hx1 hd hd1) (Real.exp_pos _).le (by positivity)
  have h := mul_le_mul_of_nonneg_left h
    (show 0 ≤ K * lowCoefficient (59 / 60) * L by positivity)
  rw [originalScalar_eq_logScalar (by linarith) K d,
    originalScalar_eq_logScalar (by norm_num : (0 : ℝ) < 3100) K d]
  unfold logScalar
  have hL0 : L ≠ 0 := by linarith
  have hid : K * lowCoefficient (59 / 60) * L *
      ((Source524.logNu (x * Real.log 3100) * (L / 3100) *
        Real.exp (-(1 / 2 : ℝ) * (x * Real.log 3100))) *
        (Real.exp (-d * 3100 / (x * Real.log 3100 + Real.log lowHeight)) / (L / 3100) ^ 2)) =
      K * lowCoefficient (59 / 60) * 3100 * Source524.logNu (x * Real.log 3100) *
        Real.exp (-(1 / 2 : ℝ) * (x * Real.log 3100)) *
          Real.exp (-d * 3100 / (x * Real.log 3100 + Real.log lowHeight)) := by
    field_simp
  rw [hid] at h
  nlinarith only [h]

theorem base_nu_bound {s : ℝ} (hs : 24 ≤ s) (hs1 : s ≤ 6 * Real.log 3100) :
    Source524.logNu s ≤ (7.56 : ℝ) :=
  (Source524.logNu_monotone hs (hs.trans hs1) hs1).trans
    (Source524.endpoint_nu.trans (by norm_num))

theorem exponent525 {s : ℝ} (hs : 24 ≤ s) :
    -(1 / 2 : ℝ) * s - 0.2067 * 3100 / (s + Real.log lowHeight) ≤ -30.52 := by
  have ht : 0 < s + Real.log lowHeight := by linarith [lowHeight_log_bounds.1]
  have hq : (35.7 - (s + Real.log lowHeight) / 2) * (s + Real.log lowHeight) ≤
      (0.2067 : ℝ) * 3100 := by
    nlinarith [sq_nonneg (s + Real.log lowHeight - 35.7)]
  have hd := (le_div_iff₀ ht).mpr hq
  linarith [lowHeight_log_bounds.2]

theorem exponent526 {s : ℝ} (hs : 24 ≤ s) :
    -(1 / 2 : ℝ) * s - 0.10367089 * 3100 / (s + Real.log lowHeight) ≤ -21.35 := by
  have ht : 0 < s + Real.log lowHeight := by linarith [lowHeight_log_bounds.1]
  have hu : s + Real.log lowHeight ≤ s + 10.36 := by linarith [lowHeight_log_bounds.2]
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 0.10367089 * 3100) ht hu
  have hq : (21.35 - s / 2) * (s + 10.36) ≤ (0.10367089 : ℝ) * 3100 := by
    nlinarith [sq_nonneg (s - 24)]
  have hdiv := (le_div_iff₀ (by linarith : 0 < s + 10.36)).mpr hq
  linarith

theorem rational525 :
    (14000 * 1.0159 * 3100 * 7.56 : ℝ) * Real.exp (-30.52) ≤ 3 / 100000 := by
  have h := Source524.exp_nat_add_lower 30 6 (u := 0.52) (by norm_num) (le_refl _)
  norm_num only [Nat.cast_ofNat, show (30 : ℝ) + 0.52 = 30.52 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
  linarith only [h]

theorem rational526 :
    (2 * 1.0159 * 3100 * 7.56 : ℝ) * Real.exp (-21.35) ≤ 3 / 100000 := by
  have h := Source524.exp_nat_add_lower 21 6 (u := 0.35) (by norm_num) (le_refl _)
  norm_num only [Nat.cast_ofNat, show (21 : ℝ) + 0.35 = 21.35 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
  linarith only [h]

theorem base_scalar_bound {K d s b : ℝ} (hK : 0 ≤ K) (hs : 24 ≤ s)
    (hs1 : s ≤ 6 * Real.log 3100)
    (hexp : -(1 / 2 : ℝ) * s - d * 3100 / (s + Real.log lowHeight) ≤ b) :
    logScalar K d 3100 s ≤ K * 1.0159 * 3100 * 7.56 * Real.exp b := by
  have hn0 := (Source524.logNu_bounds hs).2
  have h := mul_le_mul
    (mul_le_mul Source524.original_decimal_coefficients.1 (base_nu_bound hs hs1) hn0 (by norm_num))
    (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by norm_num)
  have h := mul_le_mul_of_nonneg_left h (show 0 ≤ K * 3100 by positivity)
  unfold logScalar
  rw [Real.exp_sub] at h
  rw [show -d * 3100 / (s + Real.log lowHeight) =
    -(d * 3100 / (s + Real.log lowHeight)) by ring, Real.exp_neg]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

theorem scalar525_paid (L x : ℝ) (hL : 3100 ≤ L) (hx : 3 ≤ x) (hx1 : x ≤ 6) :
    scalar525 L x ≤ (3 / 100000 : ℝ) := by
  apply (originalScalar_reduce_L (by norm_num : (0 : ℝ) ≤ 14000) hL hx hx1
    (by norm_num) (by norm_num : (0.2067 : ℝ) ≤ 0.2067)).trans
  rw [originalScalar_eq_logScalar (by norm_num : (0 : ℝ) < 3100)]
  have hs := Source524.real_parameter_scaling hL hx hx1
  have hhi : x * Real.log 3100 ≤ 6 * Real.log 3100 :=
    mul_le_mul_of_nonneg_right hx1 (Real.log_nonneg (by norm_num))
  exact (base_scalar_bound (by norm_num) hs.1 hhi (exponent525 hs.1)).trans rational525

theorem scalar526_paid (L x : ℝ) (hL : 3100 ≤ L) (hx : 3 ≤ x) (hx1 : x ≤ 6) :
    scalar526 L x ≤ (3 / 100000 : ℝ) := by
  apply (originalScalar_reduce_L (by norm_num : (0 : ℝ) ≤ 2) hL hx hx1
    (by norm_num : (0.10367089 : ℝ) ≤ 0.10367089) (by norm_num)).trans
  rw [originalScalar_eq_logScalar (by norm_num : (0 : ℝ) < 3100)]
  have hs := Source524.real_parameter_scaling hL hx hx1
  have hhi : x * Real.log 3100 ≤ 6 * Real.log 3100 :=
    mul_le_mul_of_nonneg_right hx1 (Real.log_nonneg (by norm_num))
  exact (base_scalar_bound (by norm_num) hs.1 hhi (exponent526 hs.1)).trans rational526

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526
