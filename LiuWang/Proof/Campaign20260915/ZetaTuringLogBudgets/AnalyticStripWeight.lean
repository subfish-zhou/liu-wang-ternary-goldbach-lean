import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.SourceRealBudget
import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalAngle

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourceStripArgumentCorrection (T x : ℝ) : ℝ :=
  (x - T * Real.arctan (x / T)) / 3

def sourceStripNormalizer (s : ℂ) : ℂ :=
  Complex.exp ((17 / 12 - s / 3) * Complex.log s + s / 3 +
    Complex.I * (Real.pi : ℂ) * s / 6)

def sourceStripBoundaryExponent (s : ℂ) : ℂ :=
  (5 / 4 - s) / (3 / 4) * (Real.log (253 / 100 : ℝ) : ℂ) +
    (s - 1 / 2) / (3 / 4) * (realLogZeta (5 / 4) : ℂ)

def sourceStripQuotient (s : ℂ) : ℂ :=
  (s - 1) * riemannZeta s /
    (sourceStripNormalizer s * Complex.exp (sourceStripBoundaryExponent s))

theorem arctan_cubic_bounds {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x ∧ Real.arctan x ≤ x := by
  have hc : Continuous (fun y : ℝ => 1 / (1 + y ^ 2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro y
    exact (show 0 < (1 : ℝ) + y ^ 2 by positivity).ne'
  have hi := hc.intervalIntegrable 0 x (μ := volume)
  have hlo := intervalIntegral.integral_mono_on hx
    ((by fun_prop : Continuous (fun y : ℝ => 1 - y ^ 2)).intervalIntegrable _ _)
    hi (fun y _ => by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + y ^ 2)]
      nlinarith [sq_nonneg (y ^ 2)])
  have hhi := intervalIntegral.integral_mono_on hx hi intervalIntegrable_const
    (fun y _ => by
      rw [div_le_one (by positivity : (0 : ℝ) < 1 + y ^ 2)]
      nlinarith)
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous (fun y : ℝ => y ^ 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_pow, integral_one_div_one_add_sq] at hlo
  rw [integral_one_div_one_add_sq, intervalIntegral.integral_const] at hhi
  norm_num at hlo hhi
  exact ⟨by linarith, hhi⟩

theorem sourceStripArgumentCorrection_bounds {T x : ℝ} (hT : 0 < T) (hx : 0 ≤ x) :
    0 ≤ sourceStripArgumentCorrection T x ∧
      sourceStripArgumentCorrection T x ≤ x ^ 3 / (9 * T ^ 2) := by
  have h := arctan_cubic_bounds (div_nonneg hx hT.le)
  have hlo := mul_le_mul_of_nonneg_left h.1 hT.le
  have hhi := mul_le_mul_of_nonneg_left h.2 hT.le
  have he : T * (x / T) = x := by field_simp
  have hc : T * ((x / T) ^ 3 / 3) = x ^ 3 / (3 * T ^ 2) := by field_simp
  rw [mul_sub, he, hc] at hlo
  rw [he] at hhi
  have hd : x ^ 3 / (9 * T ^ 2) = (x ^ 3 / (3 * T ^ 2)) / 3 := by ring
  rw [hd]
  unfold sourceStripArgumentCorrection
  constructor <;> linarith

theorem integral_sourceStripArgumentCorrection {T : ℝ} (hT : 0 < T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceStripArgumentCorrection T x) ≤
      203 / (3072 * T ^ 2) := by
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)
    ((by unfold sourceStripArgumentCorrection; fun_prop :
      Continuous (sourceStripArgumentCorrection T)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => x ^ 3 / (9 * T ^ 2))).intervalIntegrable _ _)
    (fun x hx => (sourceStripArgumentCorrection_bounds hT (by linarith [hx.1])).2)
  rw [intervalIntegral.integral_div, integral_pow] at h
  norm_num at h
  convert! h using 1
  field_simp
  norm_num

theorem sourceStripNormalizer_ne_zero (s : ℂ) : sourceStripNormalizer s ≠ 0 :=
  Complex.exp_ne_zero _

theorem sourceStripNormalizer_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ sourceStripNormalizer s := by
  have hlog := Complex.differentiableAt_log (show s ∈ Complex.slitPlane from Or.inl hs)
  unfold sourceStripNormalizer
  fun_prop

theorem sourceStripNormalizer_norm {s : ℂ} (hs : 0 < s.re) (ht : 0 < s.im) :
    ‖sourceStripNormalizer s‖ =
      ‖s‖ ^ (17 / 12 - s.re / 3) *
        Real.exp (sourceStripArgumentCorrection s.im s.re) := by
  have hn : s ≠ 0 := by intro h; simp [h] at hs
  have harg : Complex.arg s = Real.pi / 2 - Real.arctan (s.re / s.im) := by
    have h1 := log_im_of_re_pos hs
    have h2 := Real.arctan_inv_of_pos (div_pos hs ht)
    rw [inv_div] at h2
    rw [Complex.log_im] at h1
    linarith
  rw [sourceStripNormalizer, Complex.norm_exp,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hn), ← Real.exp_add]
  congr 1
  simp [mul_re, div_ofNat_re, div_ofNat_im, Complex.log_re, Complex.log_im,
    sourceStripArgumentCorrection, harg]
  ring

theorem sourceStripNormalizer_norm_lower {s : ℂ} (hs : 0 < s.re) (ht : 0 < s.im) :
    ‖s‖ ^ (17 / 12 - s.re / 3) ≤ ‖sourceStripNormalizer s‖ := by
  rw [sourceStripNormalizer_norm hs ht]
  exact le_mul_of_one_le_right (Real.rpow_nonneg (norm_nonneg s) _)
    (Real.one_le_exp (sourceStripArgumentCorrection_bounds ht hs.le).1)

theorem sourceStripQuotient_differentiableAt {s : ℂ} (hs : 0 < s.re) (ht : 0 < s.im) :
    DifferentiableAt ℂ sourceStripQuotient s := by
  have hn : s ≠ 1 := by intro h; simp [h] at ht
  have hd := sourceStripNormalizer_differentiableAt hs
  have hb : Differentiable ℂ sourceStripBoundaryExponent := by
    unfold sourceStripBoundaryExponent
    fun_prop
  unfold sourceStripQuotient
  exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hn)).div
    (hd.mul hb.differentiableAt.cexp)
    (mul_ne_zero (sourceStripNormalizer_ne_zero s) (Complex.exp_ne_zero _))

theorem sourceStripQuotient_right_boundary {s : ℂ} (hs : s.re = 5 / 4) (ht : 0 < s.im) :
    ‖sourceStripQuotient s‖ ≤ 1 := by
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hD := sourceStripNormalizer_norm_lower hs0 ht
  norm_num [hs] at hD
  have hB : (sourceStripBoundaryExponent s).re = realLogZeta (5 / 4) := by
    norm_num [sourceStripBoundaryExponent, div_re, div_im, mul_re, mul_im,
      normSq_apply, hs]
  have hz := norm_zeta_le_real (x := 5 / 4) (by norm_num) hs.ge
  have hzpos : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
    linarith [one_le_norm_zeta_real (x := 5 / 4) (by norm_num)]
  have he : Real.exp (realLogZeta (5 / 4)) = ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ :=
    Real.exp_log hzpos
  have hnorm : ‖s - 1‖ ≤ ‖s‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [Complex.sq_norm, Complex.normSq_apply, hs]
    norm_num
  rw [sourceStripQuotient, norm_div, norm_mul, norm_mul, Complex.norm_exp, hB, he]
  apply (div_le_one (mul_pos (norm_pos_iff.mpr (sourceStripNormalizer_ne_zero s)) hzpos)).mpr
  exact (mul_le_mul hnorm hz (norm_nonneg _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hD hzpos.le)

#print axioms integral_sourceStripArgumentCorrection
#print axioms sourceStripNormalizer_norm
#print axioms sourceStripQuotient_differentiableAt
#print axioms sourceStripQuotient_right_boundary

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
