import LiuWang.Proof.Campaign20260915.Totient.RSCountAbel
import LiuWang.Proof.Campaign20260915.Totient.RSTheorem27Coefficient

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPhiSlope (m : ℕ) (L t : ℝ) : ℝ :=
  rsPhi m L t / t * (L / (rsR * Real.log t ^ 2) - (m + 1))

theorem rsPhi_hasDerivAt (m : ℕ) (L : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (rsPhi m L) (rsPhiSlope m L t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have hR := rsR_pos
  have hd := (((hasDerivAt_const t L).div
    ((Real.hasDerivAt_log ht0.ne').const_mul rsR)
    (mul_ne_zero hR.ne' hl.ne')).neg.exp).div
      (hasDerivAt_pow (m + 1) t) (pow_ne_zero _ ht0.ne')
  convert! hd using 1
  unfold rsPhiSlope rsPhi
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.neg_apply, Pi.div_apply]
  field_simp
  ring

theorem rsPhiSlope_continuousOn (m : ℕ) (L : ℝ) :
    ContinuousOn (rsPhiSlope m L) (Ioi 1) := by
  intro t ht
  have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hR : rsR ≠ 0 := rsR_pos.ne'
  have hden : rsR * Real.log t ≠ 0 := mul_ne_zero hR hl
  have hden2 : rsR * Real.log t ^ 2 ≠ 0 := mul_ne_zero hR (pow_ne_zero _ hl)
  have hp : t ^ (m + 1) ≠ 0 := pow_ne_zero _ ht0
  apply ContinuousAt.continuousWithinAt
  unfold rsPhiSlope rsPhi
  fun_prop

theorem rsPhi_pos (m : ℕ) (L : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < rsPhi m L t := by unfold rsPhi; positivity

theorem rsPhi_le_power (m : ℕ) {L t : ℝ} (hL : 0 ≤ L) (ht : 1 < t) :
    rsPhi m L t ≤ 1 / t ^ (m + 1) := by
  unfold rsPhi
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (div_nonneg hL (mul_pos rsR_pos (Real.log_pos ht)).le)

theorem rsPhiSlope_nonpos {m : ℕ} {K L t : ℝ}
    (hK : 1 < K) (hKt : K ≤ t)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2) :
    rsPhiSlope m L t ≤ 0 := by
  have ht : 1 < t := hK.trans_le hKt
  have hl := Real.log_le_log (lt_trans zero_lt_one hK) hKt
  have hs := pow_le_pow_left₀ (Real.log_pos hK).le hl 2
  have hden : 0 < rsR * Real.log t ^ 2 := mul_pos rsR_pos (sq_pos_of_pos (Real.log_pos ht))
  have hq : L / (rsR * Real.log t ^ 2) ≤ (m : ℝ) + 1 := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2 := hupper
      _ ≤ _ := by
        have hR := rsR_pos
        nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ ((m : ℝ) + 1) * rsR)]
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (rsPhi_pos m L (lt_trans zero_lt_one ht)).le (lt_trans zero_lt_one ht).le)
    (sub_nonpos.mpr hq)

theorem rsPhi_antitoneOn {m : ℕ} {K L : ℝ} (hK : 1 < K)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2) :
    AntitoneOn (rsPhi m L) (Ici K) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici K)
  · intro t ht
    exact (rsPhi_hasDerivAt m L (hK.trans_le ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (rsPhi_hasDerivAt m L (hK.trans_le (interior_subset ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(rsPhi_hasDerivAt m L (hK.trans_le (interior_subset ht))).deriv]
    exact rsPhiSlope_nonpos hK (interior_subset ht) hupper

theorem rs_positiveCount_phi_abel {K T L : ℝ} (hK : 1 < K) (hKT : K ≤ T) (m : ℕ) :
    rsPositiveWindowSum (rsPhi m L) K T =
      (LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount T : ℝ) * rsPhi m L T -
      (LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount K : ℝ) * rsPhi m L K -
      ∫ t in K..T, (LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount t : ℝ) *
        rsPhiSlope m L t :=
  rs_positiveCount_abel hKT (fun _ ht => rsPhi_hasDerivAt m L (hK.trans_le ht.1))
    ((rsPhiSlope_continuousOn m L).mono (fun _ ht => hK.trans_le ht.1))

theorem rsQ_antitoneOn : AntitoneOn rsQ (Ici rsA) := by
  intro a ha b hb hab
  change rsA ≤ a at ha
  change rsA ≤ b at hb
  have ha0 : 0 < a := (by linarith [rsA_ge_thousand] : 0 < rsA).trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hal : 0 < Real.log a := Real.log_pos (by linarith [rsA_ge_thousand])
  have hbl : 0 < Real.log b := Real.log_pos (by linarith [rsA_ge_thousand])
  have haq : 0 < Real.log (a / (2 * Real.pi)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [rsA_ge_thousand, Real.pi_lt_four]
  have hbq : 0 < Real.log (b / (2 * Real.pi)) :=
    haq.trans_le (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hab (by positivity)))
  have he (t : ℝ) (ht : 0 < t) (hl : 0 < Real.log t)
      (hq : 0 < Real.log (t / (2 * Real.pi))) :
      rsQ t = 1 / (2 * Real.pi) + 0.137 / (t * Real.log (t / (2 * Real.pi))) +
        0.443 / (t * Real.log t * Real.log (t / (2 * Real.pi))) := by
    unfold rsQ
    field_simp
    ring
  rw [he a ha0 hal haq, he b hb0 hbl hbq]
  have hl := Real.log_le_log ha0 hab
  have hq := Real.log_le_log (by positivity : 0 < a / (2 * Real.pi))
    (div_le_div_of_nonneg_right hab (by positivity))
  gcongr

#print axioms rsPhi_hasDerivAt
#print axioms rsPhiSlope_continuousOn
#print axioms rsPhi_pos
#print axioms rsPhi_le_power
#print axioms rsPhiSlope_nonpos
#print axioms rsPhi_antitoneOn
#print axioms rs_positiveCount_phi_abel
#print axioms rsQ_antitoneOn

end LiuWang.Proof.Campaign20260915.Totient
