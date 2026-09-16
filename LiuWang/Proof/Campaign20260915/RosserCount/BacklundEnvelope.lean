import LiuWang.Proof.Campaign20260915.RosserCount.BacklundJensen

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter Metric MeasureTheory MeromorphicOn Real
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient

def backlundCircleEnvelope (T : ℝ) (s : ℂ) : ℝ :=
  max (Real.log ‖riemannZeta (s + 5 / 4 + (T : ℂ) * I)‖)
    (Real.log ‖riemannZeta (s + 5 / 4 - (T : ℂ) * I)‖)

theorem backlundBranch_analyticOnNhd {T : ℝ} (hT : rsA ≤ |T|) :
    AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta (s + 5 / 4 + (T : ℂ) * I))
      (closedBall 0 (33 / 25 : ℝ)) := by
  intro s hs
  have hs' : ‖s‖ ≤ (33 / 25 : ℝ) := by simpa using hs
  have hne : s + 5 / 4 + (T : ℂ) * I ≠ 1 := by
    intro he
    have hi : s.im + T = 0 := by simpa using congrArg Complex.im he
    have hsmall : |T| ≤ (33 / 25 : ℝ) := by
      rw [show T = -s.im by linarith, abs_neg]
      exact (abs_im_le_norm s).trans hs'
    linarith [rsA_ge_thousand]
  exact (LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hne).comp
    (f := fun z : ℂ => z + 5 / 4 + (T : ℂ) * I)
    (show AnalyticAt ℂ (fun z : ℂ => z + 5 / 4 + (T : ℂ) * I) s by fun_prop)

private theorem circleIntegrable_max {f g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (fun z => max (f z) (g z)) c R := by
  convert! (((hf.add hg).add (hf.sub hg).abs).const_smul (a := (1 / 2 : ℝ))) using 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.abs_apply, Pi.sub_apply]
  rcases le_total (f z) (g z) with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem backlundCircleEnvelope_circleIntegrable {T : ℝ} (hT : rsA ≤ T) :
    CircleIntegrable (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) := by
  have hp := backlundBranch_analyticOnNhd (hT.trans (le_abs_self T))
  have hm := backlundBranch_analyticOnNhd
    (show rsA ≤ |(-T)| by simpa only [abs_neg] using hT.trans (le_abs_self T))
  have hip : CircleIntegrable
      (fun s => Real.log ‖riemannZeta (s + 5 / 4 + (T : ℂ) * I)‖) 0 (33 / 25 : ℝ) := by
    apply MeromorphicOn.circleIntegrable_log_norm
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] using
      (hp.mono sphere_subset_closedBall).meromorphicOn
  have him : CircleIntegrable
      (fun s => Real.log ‖riemannZeta (s + 5 / 4 - (T : ℂ) * I)‖) 0 (33 / 25 : ℝ) := by
    have hh : MeromorphicOn (fun s : ℂ => riemannZeta (s + 5 / 4 + (-T : ℂ) * I))
        (sphere 0 |(33 / 25 : ℝ)|) := by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25), ofReal_neg] using
        (hm.mono sphere_subset_closedBall).meromorphicOn
    simpa only [ofReal_neg, neg_mul, ← sub_eq_add_neg] using hh.circleIntegrable_log_norm
  exact circleIntegrable_max hip him

theorem norm_backlundAux_le_max_pow (T : ℝ) (n : ℕ) (s : ℂ) :
    ‖backlundAux T n s‖ ≤
      max ‖riemannZeta (s + 5 / 4 + (T : ℂ) * I)‖
        ‖riemannZeta (s + 5 / 4 - (T : ℂ) * I)‖ ^ n := by
  let a := riemannZeta (s + 5 / 4 + (T : ℂ) * I)
  let b := riemannZeta (s + 5 / 4 - (T : ℂ) * I)
  have ha := pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ ‖b‖) n
  have hb := pow_le_pow_left₀ (norm_nonneg b) (le_max_right ‖a‖ ‖b‖) n
  have hh := norm_add_le (a ^ n) (b ^ n)
  rw [norm_pow, norm_pow] at hh
  change ‖(a ^ n + b ^ n) / 2‖ ≤ max ‖a‖ ‖b‖ ^ n
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  linarith

theorem log_norm_backlundAux_le_envelope (T : ℝ) (n : ℕ) {s : ℂ}
    (hs : backlundAux T n s ≠ 0) :
    Real.log ‖backlundAux T n s‖ ≤ (n : ℝ) * backlundCircleEnvelope T s := by
  have hh := Real.log_le_log (norm_pos_iff.mpr hs) (norm_backlundAux_le_max_pow T n s)
  rw [Real.log_pow] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  unfold backlundCircleEnvelope
  rcases le_total ‖riemannZeta (s + 5 / 4 + (T : ℂ) * I)‖
    ‖riemannZeta (s + 5 / 4 - (T : ℂ) * I)‖ with h | h
  · rw [max_eq_right h]
    exact le_max_right _ _
  · rw [max_eq_left h]
    exact le_max_left _ _

theorem backlundAux_circleAverage_le_envelope {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) :
    circleAverage (fun s => Real.log ‖backlundAux T n s‖) 0 (33 / 25 : ℝ) ≤
      (n : ℝ) * circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) := by
  have hne : ∀ᶠ s in codiscreteWithin (closedBall 0 (33 / 25 : ℝ)),
      backlundAux T n s ≠ 0 := by
    rcases (backlundAux_analyticOnNhd hT n).eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_closedBall (0 : ℂ) (33 / 25 : ℝ)).isPreconnected with hz | hz
    · exact (hn (hz (by norm_num : (0 : ℂ) ∈ closedBall 0 (33 / 25 : ℝ)))).elim
    · exact hz
  have hcircle : ∀ᶠ s in codiscreteWithin (sphere 0 |(33 / 25 : ℝ)|),
      backlundAux T n s ≠ 0 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)]
    exact codiscreteWithin_mono sphere_subset_closedBall hne
  let f : ℂ → ℝ := fun s => Real.log ‖backlundAux T n s‖
  let g : ℂ → ℝ := fun s => (n : ℝ) * backlundCircleEnvelope T s
  have he : f =ᶠ[codiscreteWithin (sphere 0 |(33 / 25 : ℝ)|)]
      (fun s => min (f s) (g s)) := by
    filter_upwards [hcircle] with s hs
    exact (min_eq_left (log_norm_backlundAux_le_envelope T n hs)).symm
  have hi := CircleIntegrable.congr_codiscreteWithin he
    (backlundAux_circleIntegrable_log_norm hT n)
  have hg : CircleIntegrable g 0 (33 / 25 : ℝ) :=
    (backlundCircleEnvelope_circleIntegrable hT).const_smul (a := (n : ℝ))
  calc
    _ = circleAverage (fun s => min (f s) (g s)) 0 (33 / 25 : ℝ) :=
      circleAverage_congr_codiscreteWithin he (by norm_num)
    _ ≤ circleAverage g 0 (33 / 25 : ℝ) :=
      circleAverage_mono hi hg (fun s _ => min_le_right (f s) (g s))
    _ = _ := by
      simpa only [g, smul_eq_mul] using
        (circleAverage_fun_smul (a := (n : ℝ)) (f := backlundCircleEnvelope T)
          (c := 0) (R := (33 / 25 : ℝ)))

theorem backlundAux_divisor_envelope_bound {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) :
    (∑ᶠ z, (divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ)) z : ℝ)) ≤
      ((n : ℝ) * circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖backlundAux T n 0‖) / Real.log (44 / 25 : ℝ) := by
  refine (backlundAux_small_divisor_bound hT hn).trans ?_
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundAux_circleAverage_le_envelope hT hn) _)
    (Real.log_pos (by norm_num : (1 : ℝ) < 44 / 25)).le

theorem backlundAux_normalized_divisor_envelope {T : ℝ} (hT : rsA ≤ T) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        (∑ᶠ z, (divisor (backlundAux T (f n)) (closedBall 0 (3 / 4 : ℝ)) z : ℝ)) /
          (f n : ℝ) <
        (circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
          Real.log ‖riemannZeta (backlundCenterPoint T)‖) / Real.log (44 / 25 : ℝ) + ε := by
  obtain ⟨f, hf, hfn, hl⟩ := backlundAux_center_log_limit T
  refine ⟨f, hf, fun ε hε => ?_⟩
  have hq : 0 < Real.log (44 / 25 : ℝ) := Real.log_pos (by norm_num)
  have hnear := hl.eventually (Ioi_mem_nhds
    (sub_lt_self (Real.log ‖riemannZeta (backlundCenterPoint T)‖) (mul_pos hq hε)))
  filter_upwards [hf.eventually (eventually_ge_atTop 1), hnear] with n hn hnear
  have hp : (0 : ℝ) < f n := by exact_mod_cast (by omega : 0 < f n)
  have hb := div_le_div_of_nonneg_right (backlundAux_divisor_envelope_bound hT (hfn n)) hp.le
  have he :
      (((f n : ℝ) * circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖backlundAux T (f n) 0‖) / Real.log (44 / 25 : ℝ)) / (f n : ℝ) =
      (circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖backlundAux T (f n) 0‖ / (f n : ℝ)) / Real.log (44 / 25 : ℝ) := by
    field_simp
  rw [he] at hb
  refine hb.trans_lt ?_
  apply (div_lt_iff₀ hq).mpr
  have he' :
      ((circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) / Real.log (44 / 25 : ℝ) + ε) *
        Real.log (44 / 25 : ℝ) =
      circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖ + ε * Real.log (44 / 25 : ℝ) := by
    field_simp
  rw [he']
  linarith

#print axioms backlundBranch_analyticOnNhd
#print axioms backlundCircleEnvelope_circleIntegrable
#print axioms norm_backlundAux_le_max_pow
#print axioms log_norm_backlundAux_le_envelope
#print axioms backlundAux_circleAverage_le_envelope
#print axioms backlundAux_divisor_envelope_bound
#print axioms backlundAux_normalized_divisor_envelope

end LiuWang.Proof.Campaign20260915.RosserCount
