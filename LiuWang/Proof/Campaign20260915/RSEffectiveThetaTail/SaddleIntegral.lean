import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.Parameters
import LiuWang.Proof.Campaign20260915.Totient.RSTheorem27Coefficient

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem saddle_outer_integral {s : ℝ} (hs : 16 ≤ s) :
    IntegrableOn (rsLaplace 1 (s ^ 2) (Real.log (2 * Real.pi))) (Ioi (2 * s)) ∧
      (∫ u in Ioi (2 * s), rsLaplace 1 (s ^ 2) (Real.log (2 * Real.pi)) u) ≤
        3 * s * Real.exp (-5 * s / 2) := by
  let b := Real.log (2 * Real.pi)
  have hb : (1 : ℝ) ≤ b ∧ b ≤ 2 := by
    dsimp [b]
    constructor <;> linarith [rs_log_two_pi_interval.1, rs_log_two_pi_interval.2]
  have hs0 : 0 < s := by linarith
  have hd : 0 < 2 * s - b := by linarith
  have hrec : 1 / (2 * s - b) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hr : rsLaplaceCorrection 1 (s ^ 2) b (2 * s) ≤ 1 / 3 := by
    unfold rsLaplaceCorrection
    rw [one_mul, one_mul, show s ^ 2 / (2 * s) ^ 2 = (1 / 4 : ℝ) by
      field_simp
      norm_num]
    linarith
  have hi := rsLaplace_integral_le (m := 1) (by norm_num) (sq_nonneg s)
    (by linarith : 0 < 2 * s) (by linarith : b < 2 * s)
    (by linarith : rsLaplaceCorrection 1 (s ^ 2) b (2 * s) < 1)
  refine ⟨hi.1, hi.2.trans ?_⟩
  have hphase : -(1 : ℝ) * (2 * s) - s ^ 2 / (2 * s) = -5 * s / 2 := by
    field_simp
    ring
  have hprim : rsLaplacePrimitive 1 (s ^ 2) b (2 * s) ≤
      2 * s * Real.exp (-5 * s / 2) := by
    unfold rsLaplacePrimitive
    rw [hphase]
    norm_num only [div_one, one_pow]
    exact (mul_le_mul_of_nonneg_left (show 2 * s - b + 1 ≤ 2 * s by linarith)
      (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  apply (div_le_iff₀ (by linarith : 0 < 1 - rsLaplaceCorrection 1 (s ^ 2) b (2 * s))).mpr
  have hm := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 3 * s * Real.exp (-5 * s / 2) by positivity)
  nlinarith

theorem saddle_laplace_le {s u : ℝ} (_hs : 0 ≤ s) (hu : 0 < u)
    (hb : Real.log (2 * Real.pi) ≤ u) (hu2 : u ≤ 2 * s) :
    rsLaplace 1 (s ^ 2) (Real.log (2 * Real.pi)) u ≤
      2 * s * Real.exp (-2 * s) := by
  have hphase : -(1 : ℝ) * u - s ^ 2 / u ≤ -2 * s := by
    have he : u * (s ^ 2 / u) = s ^ 2 := by field_simp
    nlinarith [sq_nonneg (u - s)]
  have hex := Real.exp_le_exp.mpr hphase
  have hb0 : 0 ≤ Real.log (2 * Real.pi) := by linarith [rs_log_two_pi_interval.1]
  unfold rsLaplace
  exact (mul_le_mul hex (show u - Real.log (2 * Real.pi) ≤ 2 * s by linarith)
    (by linarith) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem saddle_integral {s v : ℝ} (hs : 16 ≤ s) (hv : s / 2 ≤ v) (hv2 : v ≤ 2 * s) :
    IntegrableOn (rsLaplace 1 (s ^ 2) (Real.log (2 * Real.pi))) (Ioi v) ∧
      (∫ u in Ioi v, rsLaplace 1 (s ^ 2) (Real.log (2 * Real.pi)) u) ≤
        4 * s ^ 2 * Real.exp (-2 * s) := by
  let f := rsLaplace 1 (s ^ 2) (Real.log (2 * Real.pi))
  have hv0 : 0 < v := by linarith
  have hcont : ContinuousOn f (Icc v (2 * s)) := by
    intro u hu
    have hu0 : u ≠ 0 := (hv0.trans_le hu.1).ne'
    unfold f rsLaplace
    fun_prop
  have hfinite : IntervalIntegrable f volume v (2 * s) :=
    hcont.intervalIntegrable_of_Icc hv2
  have htail := saddle_outer_integral hs
  have hi : IntegrableOn f (Ioi v) := by
    rw [← Ioc_union_Ioi_eq_Ioi hv2]
    exact (hfinite.1).union htail.1
  have he : (∫ u in Ioi v, f u) = (∫ u in v..2 * s, f u) +
      ∫ u in Ioi (2 * s), f u := by
    exact (intervalIntegral.integral_interval_add_Ioi' hfinite htail.1).symm
  have hfbound : (∫ u in v..2 * s, f u) ≤
      3 * s ^ 2 * Real.exp (-2 * s) := by
    have h := intervalIntegral.integral_mono_on hv2 hfinite intervalIntegrable_const
      (fun u hu => saddle_laplace_le (by linarith : 0 ≤ s) (hv0.trans_le hu.1)
        (by linarith [hu.1, rs_log_two_pi_interval.2]) hu.2)
    rw [intervalIntegral.integral_const] at h
    simp only [smul_eq_mul] at h
    apply h.trans
    have hm := mul_le_mul_of_nonneg_right (show 2 * s - v ≤ 3 * s / 2 by linarith)
      (show 0 ≤ 2 * s * Real.exp (-2 * s) by positivity)
    nlinarith
  have htbound : (∫ u in Ioi (2 * s), f u) ≤ s ^ 2 * Real.exp (-2 * s) := by
    apply htail.2.trans
    exact mul_le_mul (by nlinarith : 3 * s ≤ s ^ 2)
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (sq_nonneg s)
  refine ⟨hi, ?_⟩
  rw [he]
  nlinarith

theorem phi_integral_selected_cutoff {L : ℝ} (hL : 5000 ≤ L) :
    IntegrableOn (fun t => rsPhi 1 L t * Real.log (t / (2 * Real.pi)))
      (Ioi (spectralCutoff L)) ∧
      (∫ t in Ioi (spectralCutoff L), rsPhi 1 L t * Real.log (t / (2 * Real.pi))) ≤
        4 * saddle L ^ 2 * Real.exp (-2 * saddle L) := by
  have hs := saddle_ge_sixteen hL
  have hs0 : 0 ≤ saddle L := by linarith
  have hr0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr : 1 ≤ Real.sqrt (2 : ℝ) ∧ Real.sqrt (2 : ℝ) ≤ 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    constructor <;> nlinarith
  have hv : saddle L / 2 ≤ saddle L / Real.sqrt 2 :=
    div_le_div_of_nonneg_left hs0 hr0 hr.2
  have hv2 : saddle L / Real.sqrt 2 ≤ 2 * saddle L := by
    apply (div_le_iff₀ hr0).mpr
    nlinarith
  have hi := saddle_integral hs hv hv2
  rw [saddle_sq (by linarith : 0 ≤ L)] at hi
  have hfun : (fun u => Real.exp u •
      (rsPhi 1 L (Real.exp u) * Real.log (Real.exp u / (2 * Real.pi)))) =
      rsLaplace 1 (L / rsR) (Real.log (2 * Real.pi)) := by
    funext u
    simpa only [smul_eq_mul, Nat.cast_one] using rs_phi_exp_change 1 L u
  have hchange := integral_comp_exp_Ioi
    (fun t => rsPhi 1 L t * Real.log (t / (2 * Real.pi))) (saddle L / Real.sqrt 2)
  have hiff := integrableOn_comp_exp_Ioi
    (fun t => rsPhi 1 L t * Real.log (t / (2 * Real.pi))) (saddle L / Real.sqrt 2)
  rw [hfun] at hchange hiff
  refine ⟨hiff.mp hi.1, ?_⟩
  change (∫ t in Ioi (Real.exp (saddle L / Real.sqrt 2)),
    rsPhi 1 L t * Real.log (t / (2 * Real.pi))) ≤ _
  rw [← hchange]
  simpa only [saddle_sq (by linarith : 0 ≤ L)] using hi.2

theorem Q_phi_integral_selected_cutoff {L : ℝ} (hL : 5000 ≤ L) :
    rsQ (spectralCutoff L) *
      (∫ t in Ioi (spectralCutoff L), rsPhi 1 L t * Real.log (t / (2 * Real.pi))) ≤
        (0.6368 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) := by
  have hK := spectralCutoff_ge_rsA hL
  have hnon : 0 ≤ ∫ t in Ioi (spectralCutoff L),
      rsPhi 1 L t * Real.log (t / (2 * Real.pi)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have ht1 : 2 * Real.pi ≤ t := by
      have h := rsA_ge_thousand.trans hK
      change spectralCutoff L < t at ht
      linarith [Real.pi_lt_four]
    have ht0 : 0 < t := (by positivity : (0 : ℝ) < 2 * Real.pi).trans_le ht1
    apply mul_nonneg (by unfold rsPhi; positivity)
    apply Real.log_nonneg
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using ht1)
  calc
    _ ≤ 0.1592 * (∫ t in Ioi (spectralCutoff L),
        rsPhi 1 L t * Real.log (t / (2 * Real.pi))) :=
      mul_le_mul_of_nonneg_right (rsQ_le_original hK) hnon
    _ ≤ 0.1592 * (4 * saddle L ^ 2 * Real.exp (-2 * saddle L)) :=
      mul_le_mul_of_nonneg_left (phi_integral_selected_cutoff hL).2 (by norm_num)
    _ = _ := by ring

#print axioms saddle_outer_integral
#print axioms phi_integral_selected_cutoff
#print axioms Q_phi_integral_selected_cutoff

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
