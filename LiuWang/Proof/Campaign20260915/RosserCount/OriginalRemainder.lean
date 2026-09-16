import LiuWang.Proof.Campaign20260915.Totient.RSTheorem27Coefficient

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient

-- Rosser (1941), p.223; the pointwise counting theorem is not assumed here.
def rosserMain (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8

def rosserError (T : ℝ) : ℝ :=
  0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588

def rosserMainSlope (T : ℝ) : ℝ :=
  Real.log (T / (2 * Real.pi)) / (2 * Real.pi)

def rosserErrorSlope (T : ℝ) : ℝ :=
  0.137 / T + 0.443 / (T * Real.log T)

theorem rosserMain_hasDerivAt {T : ℝ} (hT : 0 < T) :
    HasDerivAt rosserMain (rosserMainSlope T) T := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hd := (hasDerivAt_id T).div_const (2 * Real.pi)
  have hl := (Real.hasDerivAt_log (div_ne_zero hT.ne' hp)).comp T hd
  convert! ((hd.mul hl).sub hd).add_const (7 / 8) using 1
  unfold rosserMainSlope
  simp only [Function.comp_apply, id_eq]
  field_simp
  ring

theorem rosserError_hasDerivAt {T : ℝ} (hT : 1 < T) :
    HasDerivAt rosserError (rosserErrorSlope T) T := by
  have hT0 : T ≠ 0 := (lt_trans zero_lt_one hT).ne'
  have hl : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  have hd := Real.hasDerivAt_log hT0
  have hll := (Real.hasDerivAt_log hl).comp T hd
  convert! ((hd.const_mul (0.137 : ℝ)).add
    (hll.const_mul (0.443 : ℝ))).add_const (1.588 : ℝ) using 1
  unfold rosserErrorSlope
  field_simp

theorem rosserErrorSlope_pos {T : ℝ} (hT : 1 < T) :
    0 < rosserErrorSlope T := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hl : 0 < Real.log T := Real.log_pos hT
  unfold rosserErrorSlope
  positivity

theorem rosserErrorSlope_antitoneOn :
    AntitoneOn rosserErrorSlope (Set.Ioi 1) := by
  intro a ha b hb hab
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hal : 0 < Real.log a := Real.log_pos ha
  have hl : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  unfold rosserErrorSlope
  gcongr

theorem rosserMainSlope_add_rosserErrorSlope {T : ℝ} (hT : rsA ≤ T) :
    rosserMainSlope T + rosserErrorSlope T =
      rsQ T * Real.log (T / (2 * Real.pi)) := by
  have hT1 : 1 < T := by linarith [rsA_ge_thousand]
  have hT0 : 0 < T := lt_trans zero_lt_one hT1
  have hl : 0 < Real.log T := Real.log_pos hT1
  have hq : 0 < Real.log (T / (2 * Real.pi)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith [rsA_ge_thousand, Real.pi_lt_four]
  unfold rosserMainSlope rosserErrorSlope rsQ
  field_simp

theorem rosserUpper_hasDerivAt {T : ℝ} (hT : rsA ≤ T) :
    HasDerivAt (fun t => rosserMain t + rosserError t)
      (rsQ T * Real.log (T / (2 * Real.pi))) T := by
  have hT1 : 1 < T := by linarith [rsA_ge_thousand]
  rw [← rosserMainSlope_add_rosserErrorSlope hT]
  exact (rosserMain_hasDerivAt (lt_trans zero_lt_one hT1)).add
    (rosserError_hasDerivAt hT1)

#print axioms rosserMain_hasDerivAt
#print axioms rosserError_hasDerivAt
#print axioms rosserErrorSlope_pos
#print axioms rosserErrorSlope_antitoneOn
#print axioms rosserMainSlope_add_rosserErrorSlope
#print axioms rosserUpper_hasDerivAt

end LiuWang.Proof.Campaign20260915.RosserCount
