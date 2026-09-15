import LiuWang.Proof.ZeroRegionFamily.Sharp.ZetaKernel

/-! # 主字符实际极点与实轴负费用，保全部实高度母式 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem real_digamma_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (Complex.digamma (a : ℂ)).re ≤ (Complex.digamma (b : ℂ)).re := by
  have hh := digamma_difference_hasSum ha (ha.trans_le hab) 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hh
  have hn : ∀ n : ℕ, ((n : ℝ)+b)/(((n : ℝ)+b)^2+(0 : ℝ)^2)-
      ((n : ℝ)+a)/(((n : ℝ)+a)^2+(0 : ℝ)^2) ≤ 0 := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hna : (n : ℝ)+a ≠ 0 := by linarith
    have hnb : (n : ℝ)+b ≠ 0 := by linarith
    have hi := one_div_le_one_div_of_le (show 0 < (n : ℝ)+a by linarith)
      (show (n : ℝ)+a ≤ (n : ℝ)+b by linarith)
    have he (u : ℝ) (hu : u ≠ 0) : u/(u^2+(0 : ℝ)^2)=1/u := by field_simp; ring
    rw [he _ hna, he _ hnb]
    linarith
  have hle : (∑' n : ℕ, (((n : ℝ)+b)/(((n : ℝ)+b)^2+(0 : ℝ)^2)-
      ((n : ℝ)+a)/(((n : ℝ)+a)^2+(0 : ℝ)^2))) ≤ 0 := tsum_nonpos hn
  rw [hh.tsum_eq] at hle
  linarith

theorem real_digamma_upper :
    (Complex.digamma ((63/40 : ℝ) : ℂ)).re ≤ 18/25-Real.eulerMascheroniConstant := by
  have hh := (digamma_re_mem_approx_interval (a := 1) (by norm_num) le_rfl
    (z := (63/40 : ℂ)) (N := 4) (by norm_num) (by norm_num)).2
  norm_num [digammaApprox, sum_range_succ, Complex.norm_div,
    Complex.norm_real, Complex.norm_natCast] at hh
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith

theorem real_digamma_lower :
    13/20-Real.eulerMascheroniConstant ≤ (Complex.digamma ((9/5 : ℝ) : ℂ)).re := by
  have hp : ∀ n : ℕ, (9/5 : ℂ) ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.re hn
    norm_num at hh
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hs := Complex.hasSum_re (Complex.hasSum_digamma hp)
  have ht : ∀ n : ℕ, 0 ≤ (1/((n : ℂ)+1)-1/((n : ℂ)+(9/5 : ℂ))).re := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hh := one_div_le_one_div_of_le (show 0 < (n : ℝ)+1 by positivity)
      (show (n : ℝ)+1 ≤ (n : ℝ)+9/5 by linarith)
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_div, ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.ofReal_re] using
      (sub_nonneg.mpr hh)
  have h := hs.summable.sum_le_tsum (range 3) (fun n _ => ht n)
  rw [hs.tsum_eq] at h
  norm_num [sum_range_succ] at h
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith

theorem stechkinSigma_bounds {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    8/5 ≤ stechkinSigma sigma ∧ stechkinSigma sigma ≤ 44/25 := by
  have hh := Real.sq_sqrt (show 0 ≤ 1+4*sigma^2 by positivity)
  have hr := Real.sqrt_nonneg (1+4*sigma^2)
  have hsquare : sigma^2 ≤ (23/20 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 23/20-sigma by linarith) (show 0 ≤ 23/20+sigma by linarith)]
  dsimp [stechkinSigma]
  constructor <;> nlinarith

theorem stechkinK_le : stechkinK ≤ 9/20 := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [stechkinK]
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem shiftedGamma_real_bound {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    shiftedGammaDifference sigma 0 ≤ -159/800 := by
  have hb := stechkinSigma_bounds hs hs1
  have hu := real_digamma_mono (a := sigma/2+1) (b := 63/40) (by linarith) (by linarith)
  have hl := real_digamma_mono (a := 9/5) (b := stechkinSigma sigma/2+1)
    (by norm_num) (by linarith [hb.1])
  have h1 := mul_le_mul_of_nonneg_left
    (real_digamma_lower.trans hl) stechkinK_mem.1
  have h2 := mul_le_mul_of_nonneg_left log_pi_ge_one (sub_nonneg.mpr stechkinK_mem.2)
  have h3 := mul_le_mul_of_nonneg_left Real.one_half_lt_eulerMascheroniConstant.le
    (sub_nonneg.mpr stechkinK_mem.2)
  simp only [shiftedGammaDifference, Complex.ofReal_zero, mul_zero, add_zero]
  have hcast (u : ℝ) : (u : ℂ)/2+1=((u/2+1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, hcast]
  dsimp [stechkinConductorCoeff]
  have h4 := hu.trans real_digamma_upper
  nlinarith [stechkinK_le]

theorem shiftedGamma_all_height {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    shiftedGammaDifference sigma t ≤
      stechkinConductorCoeff*(Real.log (max 1 |t|)-Real.log Real.pi)+23/40-11*stechkinK/30 := by
  have hge := stechkinSigma_ge hs
  have hgap := stechkinSigma_sub_le hs
  have hu := digamma_shift_up_le (a := 1) (b := sigma/2+1) le_rfl (by linarith) (t/2)
  have hl := digamma_shift_down_le (a := sigma/2+1) (b := stechkinSigma sigma/2+1)
    (by linarith) (by linarith) (t/2)
  have href := digamma_one_re_le_log_max (t/2)
  norm_num only [Complex.ofReal_one] at hu
  have hlog : 2*|t/2|=|t| := by rw [abs_div]; norm_num; ring
  rw [hlog] at href
  have ha : (Complex.digamma (((sigma/2+1 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ))).re ≤
      Real.log (max 1 |t|)+23/20 := by linarith
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr stechkinK_mem.2)
  have h2 := mul_le_mul_of_nonneg_left hl stechkinK_mem.1
  have h3 := mul_le_mul_of_nonneg_left hgap stechkinK_mem.1
  have hcast (u : ℝ) : ((u : ℂ)+Complex.I*t)/2+1 =
      (((u/2+1 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ)) := by push_cast; ring
  unfold shiftedGammaDifference
  rw [hcast, hcast]
  dsimp [stechkinConductorCoeff]
  nlinarith

theorem poleDifference_real_le {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    poleDifference sigma 0 ≤ 1/(sigma-1)-11/19 := by
  have hb := stechkinSigma_bounds hs hs1
  have hp : 0 < stechkinSigma sigma-1 := by linarith [hb.1]
  have hh : 11/19 ≤ stechkinK/(stechkinSigma sigma-1) := by
    apply (le_div_iff₀ hp).mpr
    linarith [stechkinK_ge, hb.2]
  simp only [poleDifference, Complex.ofReal_zero, mul_zero, add_zero,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [div_eq_mul_inv] at hh ⊢
  linarith

theorem poleDifference_high_nonpos {sigma t : ℝ} (hs : 1 < sigma)
    (hs1 : sigma ≤ 23/20) (ht : 1 ≤ |t|) : poleDifference sigma t ≤ 0 := by
  have hb := stechkinSigma_bounds hs hs1
  have hu : 0 < sigma-1 := by linarith
  have hv : 0 < stechkinSigma sigma-1 := by linarith [hb.1]
  have ht2 : 1 ≤ t^2 := by nlinarith [sq_abs t]
  have hkv : 33/125 ≤ stechkinK*(stechkinSigma sigma-1) := by
    have hh := mul_le_mul stechkinK_ge (show 3/5 ≤ stechkinSigma sigma-1 by linarith [hb.1])
      (by norm_num) stechkinK_mem.1
    norm_num at hh
    exact hh
  have hvsq : (stechkinSigma sigma-1)^2 ≤ (19/25 : ℝ)^2 := by nlinarith [hb.1, hb.2]
  have hprod : (sigma-1)*(stechkinSigma sigma-1)^2 ≤ 3/20*(19/25 : ℝ)^2 :=
    mul_le_mul (show sigma-1 ≤ 3/20 by linarith) hvsq (sq_nonneg _) (by norm_num)
  have hY := mul_le_mul_of_nonneg_right (show sigma-1 ≤ 3/20 by linarith) (sq_nonneg t)
  have hbig := mul_le_mul_of_nonneg_right hkv (sq_nonneg t)
  have hpos : 0 ≤ stechkinK*(stechkinSigma sigma-1)*(sigma-1)^2 := by positivity
  simp only [poleDifference, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, one_mul, sub_zero, add_zero, zero_add]
  apply sub_nonpos.mpr
  rw [← mul_div_assoc, div_le_div_iff₀
    (by nlinarith [sq_nonneg (sigma-1)])
    (by nlinarith [sq_nonneg (stechkinSigma sigma-1)])]
  nlinarith

theorem zeta_real_strong {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    zetaDamped sigma 0 ≤ 1/(sigma-1)-3/4 := by
  linarith [zeta_damped_pole_bound hs 0, shiftedGamma_real_bound hs hs1,
    poleDifference_real_le hs hs1]

theorem zeta_real_function {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    zetaDamped sigma 0 ≤ 1/(sigma-1)-stechkinK/(stechkinSigma sigma-1)-159/800 := by
  have hh := zeta_damped_pole_bound hs 0
  have hg := shiftedGamma_real_bound hs hs1
  simp only [poleDifference, Complex.ofReal_zero, mul_zero, add_zero,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re] at hh
  simp only [div_eq_mul_inv] at hh ⊢
  linarith

theorem principal_real_strong {q : ℕ} [NeZero q]
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK 0 ≤
      1/(sigma-1)-3/4-principalPrimeCost q sigma := by
  rw [principal_real_damped_identity hs]
  have hh := zeta_real_strong hs hs1
  simpa [zetaDamped] using sub_le_sub_right hh (principalPrimeCost q sigma)

theorem principal_all_height {q : ℕ} [NeZero q]
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK t ≤
      poleDifference sigma t+
      stechkinConductorCoeff*(Real.log (max 1 |t|)-Real.log Real.pi)+
        23/40-11*stechkinK/30+principalPrimeCost q sigma := by
  have he := principal_damped_euler_bound (q := q) hs t
  have hz := zeta_damped_pole_bound hs t
  have hg := shiftedGamma_all_height hs hs1 t
  dsimp [zetaDamped] at hz
  linarith

theorem principal_high {q : ℕ} [NeZero q]
    {sigma t : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (ht : 1 ≤ |t|) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK t ≤
      stechkinConductorCoeff*(Real.log |t|-Real.log Real.pi)+
        23/40-11*stechkinK/30+principalPrimeCost q sigma := by
  have hh := principal_all_height (q := q) hs hs1 t
  rw [max_eq_right ht] at hh
  linarith [poleDifference_high_nonpos hs hs1 ht]

end LiuWang.Proof.ZeroRegionFamily.Sharp
