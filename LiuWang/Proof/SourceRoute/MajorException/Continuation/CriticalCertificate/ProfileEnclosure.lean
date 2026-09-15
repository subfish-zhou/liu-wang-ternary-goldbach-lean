import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.ElementaryBounds

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

def nuLo (ll lh : ℝ) : ℝ := 1.78107239*ll+2.50637/lh
def nuHi (ll lh : ℝ) : ℝ := 1.78107245*lh+2.50637/ll
def nuDLo (t ll : ℝ) : ℝ := 1.78107239/t-2.50637/(t*ll^2)
def nuDHi (t lh : ℝ) : ℝ := 1.78107245/t-2.50637/(t*lh^2)
def scaleLo (j : PureKind) : ℝ := zeroPower j*3.14159265358979323846*3100/0.4923
def scaleHi (j : PureKind) : ℝ := zeroPower j*3.14159265358979323847*3100/0.4923
def derivativeLo (j : PureKind) (t ll lh el : ℝ) : ℝ :=
  -decayPower j+2*nuDLo t ll/nuHi ll lh+
    scaleLo j*(el^8/t^2)*(1/2+2/t)
def derivativeHi (j : PureKind) (t ll lh eh : ℝ) : ℝ :=
  -decayPower j+2*nuDHi t lh/nuLo ll lh+
    scaleHi j*(eh^8/t^2)*(1/2+2/t)

theorem logNu_interval {t ll lh : ℝ} (ht : 1 < t) (hll : 0 < ll)
    (hl : ll ≤ Real.log t) (hh : Real.log t ≤ lh) :
    nuLo ll lh ≤ logNu t ∧ logNu t ≤ nuHi ll lh := by
  have hlog := Real.log_pos ht
  have hlh : 0 < lh := hlog.trans_le hh
  dsimp [logNu, nuLo, nuHi]
  constructor
  · apply add_le_add
    · exact mul_le_mul gammaFactor_interval.1 hl hll.le (by dsimp [gammaFactor]; positivity)
    · exact div_le_div_of_nonneg_left (by norm_num) hlog hh
  · apply add_le_add
    · exact mul_le_mul gammaFactor_interval.2 hh hlog.le (by norm_num)
    · exact div_le_div_of_nonneg_left (by norm_num) hll hl

theorem logNuD_interval {t ll lh : ℝ} (ht : 1 < t) (hll : 0 < ll)
    (hl : ll ≤ Real.log t) (hh : Real.log t ≤ lh) :
    nuDLo t ll ≤ logNuD t ∧ logNuD t ≤ nuDHi t lh := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_pos ht
  dsimp [logNuD, nuDLo, nuDHi]
  constructor
  · apply sub_le_sub (div_le_div_of_nonneg_right gammaFactor_interval.1 ht0.le)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hll.le hl 2) ht0.le
  · apply sub_le_sub (div_le_div_of_nonneg_right gammaFactor_interval.2 ht0.le)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog.le hh 2) ht0.le

theorem attenuation_interval {t el eh : ℝ} (_ht : 0 < t) (hel : 0 ≤ el)
    (he : el ≤ Real.exp (-t/16) ∧ Real.exp (-t/16) ≤ eh) :
    el^8/t^2 ≤ attenuation t ∧ attenuation t ≤ eh^8/t^2 := by
  have h := exp_nat_scale (m := 8) hel he
  have heq : (8 : ℝ)*(-t/16) = -t/2 := by ring
  rw [Nat.cast_ofNat, heq] at h
  exact ⟨div_le_div_of_nonneg_right h.1 (sq_nonneg t),
    div_le_div_of_nonneg_right h.2 (sq_nonneg t)⟩

theorem scale_interval (j : PureKind) :
    scaleLo j ≤ zeroScale j 3100 ∧ zeroScale j 3100 ≤ scaleHi j := by
  have hk : 0 ≤ zeroPower j := by cases j <;> norm_num [zeroPower]
  dsimp [scaleLo, scaleHi, zeroScale]
  constructor
  · gcongr
    exact pi_interval.1
  · gcongr
    exact pi_interval.2

theorem derivative_interval (j : PureKind) {t ll lh el eh : ℝ}
    (ht : 1 < t) (hll : 0 < ll) (hel : 0 ≤ el)
    (hl : ll ≤ Real.log t) (hh : Real.log t ≤ lh)
    (he : el ≤ Real.exp (-t/16) ∧ Real.exp (-t/16) ≤ eh)
    (hd0 : 0 ≤ nuDLo t ll) :
    derivativeLo j t ll lh el ≤ profileLogDerivative j 3100 t ∧
      profileLogDerivative j 3100 t ≤ derivativeHi j t ll lh eh := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_pos ht
  have hlh : 0 < lh := hlog.trans_le hh
  have hv := logNu_interval ht hll hl hh
  have hd := logNuD_interval ht hll hl hh
  have ha := attenuation_interval ht0 hel he
  have hk := scale_interval j
  have hvlo : 0 < nuLo ll lh := by dsimp [nuLo]; positivity
  have hv0 := logNu_pos ht
  have hdpos : 0 ≤ logNuD t := hd0.trans hd.1
  have hklo : 0 ≤ scaleLo j := by cases j <;> norm_num [scaleLo, zeroPower]
  have hkhi : 0 ≤ scaleHi j := by cases j <;> norm_num [scaleHi, zeroPower]
  have ha0 : 0 ≤ attenuation t := by dsimp [attenuation]; positivity
  have hs : 0 ≤ (1/2 : ℝ)+2/t := by positivity
  dsimp [derivativeLo, derivativeHi, profileLogDerivative, attenuationSlope]
  constructor
  · apply add_le_add
    · apply add_le_add le_rfl
      exact (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hd0) hv0 hv.2).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd.1 (by norm_num)) hv0.le)
    · apply mul_le_mul_of_nonneg_right _ hs
      exact mul_le_mul hk.1 ha.1 (by positivity) (zeroScale_pos j (by norm_num)).le
  · apply add_le_add
    · apply add_le_add le_rfl
      exact (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hdpos) hvlo hv.1).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd.2 (by norm_num)) hvlo.le)
    · apply mul_le_mul_of_nonneg_right _ hs
      exact mul_le_mul hk.2 ha.2 ha0 hkhi

theorem profile_bracket_bound (j : PureKind) {a b ll lh eh el z : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hll : 0 < ll)
    (hloglo : ll ≤ Real.log a) (hloghi : Real.log b ≤ lh)
    (heh : Real.exp (-a/16) ≤ eh) (hel : 0 ≤ el)
    (helo : el ≤ Real.exp (-b/16))
    (hz : -(scaleLo j*(el^8/b^2)) ≤ z)
    {t : ℝ} (hta : a ≤ t) (htb : t ≤ b) :
    conductorProfile j 3100 t ≤
      eh^(match j with | .linear => 24 | .quadratic => 16 | .cubic => 8) *
        (nuHi ll lh)^2 * Real.exp z := by
  have ht : 1 < t := ha.trans_le hta
  have hb : 0 < b := by linarith
  have ht0 : 0 < t := by linarith
  have hlogL : ll ≤ Real.log t :=
    hloglo.trans (Real.log_le_log (by linarith) hta)
  have hlogH : Real.log t ≤ lh :=
    (Real.log_le_log ht0 htb).trans hloghi
  have hv := (logNu_interval ht hll hlogL hlogH).2
  have he : Real.exp (-t/16) ≤ eh :=
    (Real.exp_le_exp.mpr (by linarith)).trans heh
  have heh0 : 0 ≤ eh := (Real.exp_pos _).le.trans he
  have hpower : Real.exp (-decayPower j*t) ≤
      eh^(match j with | .linear => 24 | .quadratic => 16 | .cubic => 8) := by
    have h := fun m : ℕ => (exp_nat_scale (m := m) (lo := 0) (by norm_num)
      ⟨(Real.exp_pos _).le, he⟩).2
    cases j
    · convert h 24 using 1
      dsimp [decayPower]
      congr 1
      ring
    · convert h 16 using 1
      dsimp [decayPower]
      congr 1
      ring
    · convert h 8 using 1
      dsimp [decayPower]
      congr 1
      ring
  have hat : el^8/b^2 ≤ attenuation t :=
    (attenuation_interval hb hel ⟨helo, le_rfl⟩).1.trans
      (attenuation_antitone.antitoneOn ht0 hb htb)
  have hscale := (scale_interval j).1
  have hk0 : 0 ≤ scaleLo j := by cases j <;> norm_num [scaleLo, zeroPower]
  have hproduct := mul_le_mul hscale hat (by positivity) (zeroScale_pos j (by norm_num)).le
  have hex : Real.exp (-zeroScale j 3100*attenuation t) ≤ Real.exp z := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul (mul_le_mul hpower (pow_le_pow_left₀ (logNu_pos ht).le hv 2)
    (sq_nonneg _) (by positivity)) hex (Real.exp_pos _).le (by positivity)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
