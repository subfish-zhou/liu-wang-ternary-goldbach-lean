import LiuWang.Proof.ZeroRegionFamily.Stechkin

/-! # Stechkin反射配对核的真实标量正性 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.ZeroRegionFamily

theorem stechkinSigma_equation (sigma : ℝ) :
    (stechkinSigma sigma)^2-stechkinSigma sigma=sigma^2 := by
  have hs := Real.sq_sqrt (show 0 ≤ 1+4*sigma^2 by positivity)
  dsimp [stechkinSigma]
  nlinarith

theorem stechkin_ratio {sigma : ℝ} (hs : 1 < sigma) :
    stechkinK*(2*stechkinSigma sigma-1) ≤ 2*sigma-1 := by
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hrpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have haux := stechkinSigma_equation sigma
  have hge := stechkinSigma_ge hs
  have hsq : (2*stechkinSigma sigma-1)^2 ≤ ((2*sigma-1)*Real.sqrt 5)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ sigma-1 by linarith) (show 0 ≤ 4*sigma-1 by linarith)]
  have hh : 2*stechkinSigma sigma-1 ≤ (2*sigma-1)*Real.sqrt 5 := by
    nlinarith [mul_pos (show 0 < 2*sigma-1 by linarith) hrpos]
  dsimp [stechkinK]
  rw [one_div_mul_eq_div, div_le_iff₀ hrpos]
  exact hh

theorem pair_fraction_monotone {sigma w y : ℝ}
    (hs : 1 < sigma) (hw : 0 ≤ w) (hy : 0 ≤ y) :
    ((sigma^2+w)+y)/(((sigma^2+w)-y)^2+(4*sigma^2+1)*y) ≤
      ((sigma^2-sigma+w)+y)/
        (((sigma^2-sigma+w)-y)^2+(2*sigma-1)^2*y) := by
  let A := sigma^2-sigma+w
  let B := sigma^2+w
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [mul_pos (show 0 < sigma by linarith) (show 0 < sigma-1 by linarith)]
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < (A-y)^2+(2*sigma-1)^2*y := by
    by_cases hz : y=0
    · simp [hz, sq_pos_of_pos hA]
    · have hyy : 0 < y := lt_of_le_of_ne hy (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos (sq_pos_of_pos (by linarith)) hyy)
  have hE : 0 < (B-y)^2+(4*sigma^2+1)*y := by
    by_cases hz : y=0
    · simp [hz, sq_pos_of_pos hB]
    · have hyy : 0 < y := lt_of_le_of_ne hy (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by positivity) hyy)
  change (B+y)/((B-y)^2+(4*sigma^2+1)*y) ≤
    (A+y)/((A-y)^2+(2*sigma-1)^2*y)
  rw [div_le_div_iff₀ hE hD]
  have hid :
      (A+y)*((B-y)^2+(4*sigma^2+1)*y)-
      (B+y)*((A-y)^2+(2*sigma-1)^2*y) =
        sigma*(A*B+(2*sigma^2-sigma-1+6*w)*y+y^2) := by
    dsimp [A, B]
    ring
  have hm : 0 ≤ 2*sigma^2-sigma-1+6*w := by
    nlinarith [mul_nonneg (show 0 ≤ sigma-1 by linarith) (show 0 ≤ 2*sigma+1 by linarith)]
  have hp : 0 ≤ sigma*(A*B+(2*sigma^2-sigma-1+6*w)*y+y^2) :=
    mul_nonneg (by linarith) (add_nonneg (add_nonneg (mul_nonneg hA.le hB.le)
      (mul_nonneg hm hy)) (sq_nonneg _))
  linarith

theorem paired_kernel_identity {sigma beta t : ℝ}
    (hs : 1 < sigma) (hb : beta ∈ Set.Icc (0 : ℝ) 1) :
    (sigma-beta)/((sigma-beta)^2+t^2)+
      (sigma-1+beta)/((sigma-1+beta)^2+t^2) =
      (2*sigma-1)*((sigma^2-sigma+beta*(1-beta))+t^2)/
        (((sigma^2-sigma+beta*(1-beta))-t^2)^2+(2*sigma-1)^2*t^2) := by
  have hu : 0 < sigma-beta := by linarith [hb.2]
  have hv : 0 < sigma-1+beta := by linarith [hb.1]
  have hdu : 0 < (sigma-beta)^2+t^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (sq_nonneg _)
  have hdv : 0 < (sigma-1+beta)^2+t^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) (sq_nonneg _)
  have hd :
      ((sigma^2-sigma+beta*(1-beta))-t^2)^2+(2*sigma-1)^2*t^2 =
      ((sigma-beta)^2+t^2)*((sigma-1+beta)^2+t^2) := by ring
  rw [hd]
  field_simp
  ring

theorem stechkin_paired_kernel_nonneg {sigma beta t : ℝ}
    (hs : 1 < sigma) (hb : beta ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ ((sigma-beta)/((sigma-beta)^2+t^2)+
      (sigma-1+beta)/((sigma-1+beta)^2+t^2))-
      stechkinK*((stechkinSigma sigma-beta)/((stechkinSigma sigma-beta)^2+t^2)+
        (stechkinSigma sigma-1+beta)/((stechkinSigma sigma-1+beta)^2+t^2)) := by
  have hs1 := hs.trans_le (stechkinSigma_ge hs)
  rw [paired_kernel_identity hs hb, paired_kernel_identity hs1 hb]
  have he := stechkinSigma_equation sigma
  have hsquare : (2*stechkinSigma sigma-1)^2=4*sigma^2+1 := by nlinarith
  rw [he, hsquare]
  have hw : 0 ≤ beta*(1-beta) := mul_nonneg hb.1 (by linarith [hb.2])
  have hfrac := pair_fraction_monotone hs hw (sq_nonneg t)
  have hpos : 0 ≤ (sigma^2+beta*(1-beta)+t^2)/
      ((sigma^2+beta*(1-beta)-t^2)^2+(4*sigma^2+1)*t^2) := by positivity
  have hr := mul_le_mul_of_nonneg_right (stechkin_ratio hs) hpos
  have hmono := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 2*sigma-1 by linarith)
  apply sub_nonneg.mpr
  simpa only [mul_div_assoc, mul_assoc] using hr.trans hmono

end LiuWang.Proof.ZeroRegionFamily
