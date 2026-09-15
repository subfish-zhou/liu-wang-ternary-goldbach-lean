import LiuWang.Proof.SourceRoute.MajorException.Continuation.ConductorProfile

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

theorem log_lower_six {t : ℝ} (ht : 6 ≤ t) : 4/3 ≤ Real.log t := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show 4 ≤ t by linarith)
  have he : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_gt_d9]

theorem log_lower_eight {t : ℝ} (ht : 8 ≤ t) : 2 ≤ Real.log t := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) ht
  have he : Real.log (8 : ℝ) = 3*Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_gt_d9]

theorem logNuD_pos {t : ℝ} (ht : 6 ≤ t) : 0 < logNuD t := by
  have hu := log_lower_six ht
  have hg := gammaFactor_lower
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < Real.log t := by linarith
  have he : logNuD t =
      (gammaFactor*(Real.log t)^2-2.50637)/(t*(Real.log t)^2) := by
    dsimp [logNuD]
    field_simp
  rw [he]
  apply div_pos _ (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hg) (sq_nonneg (Real.log t))]

theorem logNuDD_neg {t : ℝ} (ht : 8 ≤ t) : logNuDD t < 0 := by
  have hu := log_lower_eight ht
  have hg := gammaFactor_lower
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < Real.log t := by linarith
  have hc : 2*Real.log t+4 ≤ (Real.log t)^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ (Real.log t)^2+2*Real.log t+2 by positivity)]
  have he : logNuDD t =
      (-gammaFactor*(Real.log t)^3+2.50637*(Real.log t+2))/
        (t^2*(Real.log t)^3) := by
    dsimp [logNuDD]
    field_simp
  rw [he]
  apply div_neg_of_neg_of_pos _ (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hg) (pow_nonneg hu0.le 3)]

theorem zeroScale_pos (j : PureKind) {L : ℝ} (hL : 0 < L) :
    0 < zeroScale j L := by
  cases j <;> dsimp [zeroScale, zeroPower] <;> positivity

theorem profileLogDerivative_strictAnti (j : PureKind) {L : ℝ} (hL : 0 < L) :
    StrictAntiOn (profileLogDerivative j L) (Set.Ici 8) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 8)
  · intro t ht
    exact (profileLogDerivative_hasDerivAt j L (by have := ht; change 8 ≤ t at this; linarith)).continuousAt.continuousWithinAt
  · intro t ht
    have ht8 : 8 ≤ t := interior_subset ht
    rw [(profileLogDerivative_hasDerivAt j L (by linarith : 1 < t)).deriv]
    have hv := logNu_pos (show 1 < t by linarith)
    have hdd := logNuDD_neg ht8
    have hfirst : 2*(logNuDD t*logNu t-logNuD t^2)/logNu t^2 < 0 :=
      div_neg_of_neg_of_pos (by nlinarith [mul_neg_of_neg_of_pos hdd hv, sq_nonneg (logNuD t)])
        (sq_pos_of_pos hv)
    have hlast : 0 < zeroScale j L*attenuation t*attenuationCurve t := by
      have hz := zeroScale_pos j hL
      have ht0 : 0 < t := by linarith
      dsimp [attenuation, attenuationCurve]
      positivity
    linarith

theorem attenuation_antitone : StrictAntiOn attenuation (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro t ht
    exact (attenuation_hasDerivAt ht.ne').continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := interior_subset ht
    rw [(attenuation_hasDerivAt ht0.ne').deriv]
    have ha : 0 < attenuation t := by dsimp [attenuation]; positivity
    have hs : 0 < attenuationSlope t := by dsimp [attenuationSlope]; positivity
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hs

theorem zeroScale_3100_bounds (j : PureKind) :
    18000 ≤ zeroScale j 3100 ∧ zeroScale j 3100 ≤ 80000 := by
  have hp := Real.pi_gt_three
  have hp' := Real.pi_lt_four
  cases j <;> norm_num [zeroScale, zeroPower] <;> constructor <;> linarith

theorem attenuation_eight_lower : (1/5184 : ℝ) ≤ attenuation 8 := by
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have he : attenuation 8 = 1/(Real.exp 4*64) := by
    dsimp [attenuation]
    norm_num
    rw [show (-4 : ℝ) = -(4 : ℝ) by rfl, Real.exp_neg]
    ring
  rw [he]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem attenuation_thirtytwo_upper :
    attenuation 32 ≤ (1/(65536*1024) : ℝ) := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le 16
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have he : attenuation 32 = 1/(Real.exp 16*1024) := by
    dsimp [attenuation]
    norm_num
    rw [show (-16 : ℝ) = -(16 : ℝ) by rfl, Real.exp_neg]
    ring
  rw [he]
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith

theorem profileLogDerivative_initial_pos (j : PureKind) {t : ℝ}
    (ht : 6 ≤ t) (ht8 : t ≤ 8) :
    0 < profileLogDerivative j 3100 t := by
  have ht0 : 0 < t := by linarith
  have hv := logNu_pos (show 1 < t by linarith)
  have hd := logNuD_pos ht
  have ha : (1/5184 : ℝ) ≤ attenuation t :=
    attenuation_eight_lower.trans
      (attenuation_antitone.antitoneOn ht0 (by norm_num) ht8)
  have hs : (1/2 : ℝ) ≤ attenuationSlope t := by
    dsimp [attenuationSlope]
    exact le_add_of_nonneg_right (by positivity)
  have hprod := mul_le_mul (zeroScale_3100_bounds j).1 ha (by norm_num)
    (zeroScale_pos j (by norm_num)).le
  have hprod2 := mul_le_mul hprod hs (by norm_num)
    (mul_nonneg (zeroScale_pos j (by norm_num)).le (by linarith : 0 ≤ attenuation t))
  have hpow : decayPower j ≤ 3/2 := by cases j <;> norm_num [decayPower]
  dsimp [profileLogDerivative]
  have hratio : 0 < 2*logNuD t/logNu t := by positivity
  nlinarith

theorem logNuD_ratio_upper {t : ℝ} (ht : 8 ≤ t) :
    logNuD t/logNu t ≤ 1/t := by
  have ht0 : 0 < t := by linarith
  have hu := log_lower_eight ht
  have hu0 : 0 < Real.log t := by linarith
  have hv := logNu_pos (show 1 < t by linarith)
  apply (div_le_div_iff₀ hv ht0).mpr
  have h1 : logNuD t*t ≤ gammaFactor := by
    dsimp [logNuD]
    field_simp
    linarith
  have h2 : gammaFactor ≤ logNu t := by
    dsimp [logNu]
    have hg := gammaFactor_lower
    have hx := mul_le_mul_of_nonneg_left (show 1 ≤ Real.log t by linarith)
      (show 0 ≤ gammaFactor by linarith)
    have hdiv : 0 ≤ 2.50637/Real.log t := by positivity
    nlinarith
  nlinarith

theorem profileLogDerivative_thirtytwo_neg (j : PureKind) :
    profileLogDerivative j 3100 32 < 0 := by
  have hratio := logNuD_ratio_upper (t := 32) (by norm_num)
  have ha := attenuation_thirtytwo_upper
  have hz := (zeroScale_3100_bounds j).2
  have hprod := mul_le_mul hz ha
    (show 0 ≤ attenuation 32 by dsimp [attenuation]; positivity) (by norm_num)
  have hs : attenuationSlope 32 = (9/16 : ℝ) := by norm_num [attenuationSlope]
  have hp : (1/2 : ℝ) ≤ decayPower j := by cases j <;> norm_num [decayPower]
  dsimp [profileLogDerivative]
  rw [hs, mul_div_assoc]
  nlinarith

theorem log987_bounds : (6 : ℝ) ≤ Real.log 987 ∧ Real.log 987 ≤ 8 := by
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 6
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  · apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.5)
      (show (2.5 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 8
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith

end LiuWang.Proof.SourceRoute.MajorException.Continuation
