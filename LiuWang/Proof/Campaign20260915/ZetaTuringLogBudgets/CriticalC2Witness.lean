import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalMainBudget
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.LogMassWitness

set_option autoImplicit false
noncomputable section
open Complex Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization

def sourceCriticalGrowthGap (eta : ℝ) : ℝ :=
  ‖riemannZeta (criticalPoint (sourceTime eta))‖ -
    (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ)

theorem sourceCriticalGrowthGap_continuous : Continuous sourceCriticalGrowthGap := by
  have ht : Continuous sourceTime := by unfold sourceTime; fun_prop
  have hp : Continuous (fun eta : ℝ => criticalPoint (sourceTime eta)) := by
    have he : (fun eta : ℝ => criticalPoint (sourceTime eta)) =
        (fun eta : ℝ => (1 / 2 : ℂ) + (sourceTime eta : ℂ) * I) := by
      funext eta
      apply Complex.ext <;> simp [criticalPoint]
    rw [he]
    unfold sourceTime
    fun_prop
  have hz : Continuous (fun eta : ℝ => riemannZeta (criticalPoint (sourceTime eta))) := by
    apply continuous_iff_continuousAt.mpr
    intro eta
    exact (differentiableAt_riemannZeta
      (criticalPoint_ne_one (sourceTime eta))).continuousAt.comp (x := eta) hp.continuousAt
  have hpow : Continuous (fun eta : ℝ => (sourceTime eta) ^ (1 / 4 : ℝ)) :=
    ht.rpow_const (fun _ => Or.inr (by norm_num))
  exact hz.norm.sub (continuous_const.mul hpow)

theorem criticalGrowth_noninteger_witness {t : ℝ} (ht : 128 * Real.pi ≤ t)
    (hbad : (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖) :
    ∃ eta : ℝ, 8 < eta ∧ (∀ k : ℤ, eta ≠ k) ∧
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) <
        ‖riemannZeta (criticalPoint (sourceTime eta))‖ := by
  let a := sourceHeightScale t
  have ha : 8 ≤ a := sourceHeightScale_original_lower ht
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hgap : 0 < sourceCriticalGrowthGap a := by
    unfold sourceCriticalGrowthGap a
    rw [sourceTime_heightScale ht0]
    linarith
  have hev := sourceCriticalGrowthGap_continuous.continuousAt.tendsto.eventually_const_lt hgap
  obtain ⟨d, hd, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  have htop : a < min (a + d) ((⌊a⌋ : ℤ) + 1 : ℝ) :=
    lt_min (by linarith) (Int.lt_floor_add_one a)
  obtain ⟨eta, he0, he1⟩ := exists_between htop
  have heD : eta < a + d := he1.trans_le (min_le_left _ _)
  have heK : eta < (⌊a⌋ : ℤ) + (1 : ℝ) := he1.trans_le (min_le_right _ _)
  have hdist : dist eta a < d := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr he0)]
    linarith
  refine ⟨eta, lt_of_le_of_lt ha he0, ?_, ?_⟩
  · intro k hk
    have hklo : (⌊a⌋ : ℤ) < k := by
      exact_mod_cast (lt_of_le_of_lt (Int.floor_le a) he0 : (⌊a⌋ : ℝ) < eta) |>.trans_eq hk
    have hkhi : k < ⌊a⌋ + 1 := by
      have h := heK
      rw [hk] at h
      exact_mod_cast h
    omega
  · have h := hnear hdist
    unfold sourceCriticalGrowthGap at h
    linarith

theorem criticalGrowth_C2_witness {t : ℝ} (ht : 128 * Real.pi ≤ t)
    (hbad : (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖) :
    ∃ eta : ℝ, 8 < eta ∧ (∀ k : ℤ, eta ≠ k) ∧
      2 < |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
        |sourceRightNormalized eta| := by
  obtain ⟨eta, he, hint, h⟩ := criticalGrowth_noninteger_witness ht hbad
  refine ⟨eta, he, hint, ?_⟩
  linarith [norm_zeta_original_C2_growth_budget he.le hint]

theorem criticalGrowth_seven_C2_witness {t : ℝ} (ht : 128 * Real.pi ≤ t)
    (hbad : (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖) :
    ∃ eta : ℝ, 8 < eta ∧ (∀ k : ℤ, eta ≠ k) ∧
      2 < |sourceSevenNormalized eta ⌊eta⌋₊| + |sourceJnNormalized eta| +
        |sourcePolynomialExteriorNormalized eta| + |sourceLeftNormalized eta| +
          |sourceRightNormalized eta| := by
  obtain ⟨eta, he, hint, h⟩ := criticalGrowth_C2_witness ht hbad
  have hc := normalized_central_seven_exact (by linarith : 0 < eta) hint
  have habs : |sourceCentralNormalized eta| ≤
      |sourceSevenNormalized eta ⌊eta⌋₊| + |sourceJnNormalized eta| +
        |sourcePolynomialExteriorNormalized eta| := by
    rw [hc]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  exact ⟨eta, he, hint, by linarith⟩

theorem horizontalLogMass_seven_C2_witness {T : ℝ} (hT : 128 * Real.pi ≤ T)
    (hbad : sourceHorizontalLogBudget T <
      LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass T) :
    ∃ eta : ℝ, 8 < eta ∧ (∀ k : ℤ, eta ≠ k) ∧
      2 < |sourceSevenNormalized eta ⌊eta⌋₊| + |sourceJnNormalized eta| +
        |sourcePolynomialExteriorNormalized eta| + |sourceLeftNormalized eta| +
          |sourceRightNormalized eta| := by
  obtain ⟨t, ht, h⟩ := horizontalLogMass_violation_critical_witness hT hbad
  exact criticalGrowth_seven_C2_witness ht h

#print axioms sourceCriticalGrowthGap_continuous
#print axioms criticalGrowth_noninteger_witness
#print axioms criticalGrowth_C2_witness
#print axioms criticalGrowth_seven_C2_witness
#print axioms horizontalLogMass_seven_C2_witness

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
