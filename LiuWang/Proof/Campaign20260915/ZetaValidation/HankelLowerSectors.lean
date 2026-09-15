import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelContinuation

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsHankelArcBetween (s : ℂ) (m : ℕ) (u a b : ℝ) : ℂ :=
  I * ∫ θ : ℝ in a..b, rsHankelLift s m (u + θ * I)

theorem rsHankelLift_analytic_lower (s : ℂ) (m : ℕ) {w : ℂ}
    (hw : Real.sin w.im < 0) : AnalyticAt ℂ (rsHankelLift s m) w := by
  apply AnalyticAt.div (by fun_prop)
    ((rsHankelDenominator_analytic _).comp (by fun_prop))
  change rsHankelDenominator (exp w) ≠ 0
  rw [ne_eq, rsHankelDenominator_zero_iff]
  rintro ⟨n, hn⟩
  have he := congrArg Complex.im hn
  have hh : (exp w).im < 0 := by rw [exp_im]; exact mul_neg_of_pos_of_neg (Real.exp_pos _) hw
  simp only [intCast_im] at he
  linarith

theorem rsHankelLift_sector_bound (s : ℂ) (m : ℕ) {u θ B : ℝ}
    (hu : 0 ≤ u) (hθ : Real.sin θ ≤ -(1 / 2)) (hB : |θ| ≤ B) :
    ‖rsHankelLift s m (u + θ * I)‖ ≤
      Real.exp (|s.im| * B) * (Real.exp u) ^ s.re *
        Real.exp (-(Real.pi * m) * Real.exp u) := by
  let w : ℂ := u + θ * I
  let q : ℂ := 2 * Real.pi * I * exp w
  have hq : q.re = -2 * Real.pi * Real.exp u * Real.sin θ := by
    simp [q, w, mul_re, mul_im, exp_im]
    ring
  have hqu : Real.pi * Real.exp u ≤ q.re := by
    rw [hq]
    nlinarith [Real.exp_pos u, Real.pi_pos,
      mul_nonneg (mul_pos Real.pi_pos (Real.exp_pos u)).le (by linarith : 0 ≤ -(1 / 2) - Real.sin θ)]
  have hone : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hq1 : 1 ≤ q.re := by nlinarith [Real.two_le_pi]
  have hd : 1 ≤ ‖rsHankelDenominator (exp w)‖ := by
    have hn := norm_sub_norm_le (exp q) (1 : ℂ)
    rw [norm_exp, norm_one] at hn
    change Real.exp q.re - 1 ≤ ‖rsHankelDenominator (exp w)‖ at hn
    linarith [Real.add_one_le_exp q.re]
  have hre : (s * w - 2 * Real.pi * I * m * exp w).re ≤
      s.re * u + |s.im| * B - (Real.pi * m) * Real.exp u := by
    have hsw : (s * w).re = s.re * u - s.im * θ := by simp [w, mul_re, mul_im]
    have hm : (2 * Real.pi * I * (m : ℂ) * exp w).re = (m : ℝ) * q.re := by
      rw [show 2 * Real.pi * I * (m : ℂ) * exp w = (m : ℂ) * q by dsimp [q]; ring]
      simp
    have him : -(s.im * θ) ≤ |s.im| * B :=
      (neg_le_abs _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hB (abs_nonneg _))
    have hmul := mul_le_mul_of_nonneg_left hqu (Nat.cast_nonneg (α := ℝ) m)
    rw [sub_re, hsw, hm]
    nlinarith
  change ‖exp (s * w - 2 * Real.pi * I * m * exp w) / rsHankelDenominator (exp w)‖ ≤ _
  rw [norm_div, norm_exp]
  calc
    _ ≤ Real.exp (s.re * u + |s.im| * B - (Real.pi * m) * Real.exp u) :=
      (div_le_self (Real.exp_nonneg _) hd).trans (Real.exp_le_exp.mpr hre)
    _ = _ := by
      rw [Real.exp_sub, Real.exp_add, neg_mul, Real.exp_neg,
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [mul_comm u s.re]
      ring

theorem rsHankelSector_majorant_tendsto {m : ℕ} (hm : 0 < m) (s : ℂ) (B : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (|s.im| * B) * (Real.exp u) ^ s.re *
      Real.exp (-(Real.pi * m) * Real.exp u)) atTop (𝓝 0) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s.re (Real.pi * m)
    (by positivity)).comp Real.tendsto_exp_atTop
  simpa only [Function.comp_def, mul_zero, ← mul_assoc] using h.const_mul (Real.exp (|s.im| * B))

theorem rsHankelArcBetween_tendsto_zero {m : ℕ} (hm : 0 < m) (s : ℂ) {a b : ℝ}
    (hθ : ∀ θ ∈ uIcc a b, Real.sin θ ≤ -(1 / 2)) :
    Tendsto (fun u : ℝ => rsHankelArcBetween s m u a b) atTop (𝓝 0) := by
  let B := max |a| |b|
  have hb := (rsHankelSector_majorant_tendsto hm s B).const_mul |b - a|
  rw [mul_zero] at hb
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [rsHankelArcBetween, norm_mul, norm_I, one_mul]
  calc
    _ ≤ (Real.exp (|s.im| * B) * (Real.exp u) ^ s.re *
        Real.exp (-(Real.pi * m) * Real.exp u)) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro θ hmem
      have hcc := uIoc_subset_uIcc hmem
      apply rsHankelLift_sector_bound s m hu (hθ θ hcc)
      rcases le_total a b with hab | hba
      · rw [uIcc_of_le hab] at hcc
        exact abs_le_max_abs_abs hcc.1 hcc.2
      · rw [uIcc_of_ge hba] at hcc
        simpa only [B, max_comm] using abs_le_max_abs_abs hcc.1 hcc.2
    _ = _ := by ring

theorem rsHankel_right_sector_sin {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (-(Real.pi / 4))) :
    Real.sin θ ≤ -(1 / 2) := by
  have h := Real.monotoneOn_sin
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    (show -(Real.pi / 4) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos]) hθ.2
  rw [Real.sin_neg, Real.sin_pi_div_four] at h
  have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

theorem rsHankel_left_sector_sin {θ : ℝ}
    (hθ : θ ∈ Icc (5 * Real.pi / 4) (3 * Real.pi / 2)) :
    Real.sin θ ≤ -(1 / 2) := by
  have h := rsHankel_right_sector_sin (θ := Real.pi - θ)
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  rwa [Real.sin_pi_sub] at h

end LiuWang.Proof.Campaign20260915.ZetaValidation
