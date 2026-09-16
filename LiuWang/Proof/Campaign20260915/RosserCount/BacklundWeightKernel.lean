import LiuWang.Proof.Campaign20260915.RosserCount.BacklundWindowCounts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Metric MeasureTheory MeromorphicOn

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient

def backlundReciprocalKernel (u : ℝ) : ℝ := 1 / (3 / 4 + u)

def backlundRightKernel (z : ℂ) (u : ℝ) : ℝ :=
  if z.im = 0 ∧ z.re ≤ 0 then
    (Set.Iic (z.re + 3 / 4)).indicator backlundReciprocalKernel u else 0

def backlundLeftKernel (z : ℂ) (u : ℝ) : ℝ :=
  if z.im = 0 ∧ z.re ≤ -3 / 4 then
    (Set.Ici (-z.re - 3 / 4)).indicator backlundReciprocalKernel u else 0

def backlundRightFlag (z : ℂ) : ℝ :=
  if z.im = 0 ∧ z.re ∈ Set.Icc (-3 / 4 : ℝ) 0 then 1 else 0

private theorem kernel_integrable {a b : ℝ} (ha : -3 / 4 < a) (hb : -3 / 4 < b) :
    IntervalIntegrable backlundReciprocalKernel volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (by fun_prop)
  intro u hu
  have hh := (lt_min ha hb).trans_le hu.1
  dsimp [backlundReciprocalKernel]
  linarith

private theorem kernel_integral {v : ℝ} (hv : 0 ≤ v) :
    (∫ u in (0 : ℝ)..v, backlundReciprocalKernel u) =
      Real.log ((3 / 4 + v) / (3 / 4)) := by
  have he := intervalIntegral.integral_comp_add_left (fun u : ℝ => 1 / u)
    (a := 0) (b := v) (3 / 4 : ℝ)
  simpa only [add_zero, backlundReciprocalKernel] using
    he.trans (integral_one_div_of_pos (by norm_num) (by linarith))

private theorem right_cut_integrable (v : ℝ) :
    IntervalIntegrable ((Set.Iic v).indicator backlundReciprocalKernel)
      volume 0 (57 / 100) := by
  have hi := kernel_integrable (by norm_num : (-3 / 4 : ℝ) < 0)
    (by norm_num : (-3 / 4 : ℝ) < 57 / 100)
  exact ⟨hi.1.indicator measurableSet_Iic, hi.2.indicator measurableSet_Iic⟩

private theorem left_cut_integral {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) (57 / 100)) :
    (∫ u in (0 : ℝ)..57 / 100,
      (Set.Ici v).indicator backlundReciprocalKernel u) =
        Real.log ((33 / 25 : ℝ) / (3 / 4 + v)) := by
  have hv0 : 0 ≤ v := hv.1
  have he :
      (∫ u in (0 : ℝ)..57 / 100,
        (Set.Ici v).indicator backlundReciprocalKernel u) =
      ∫ u in (0 : ℝ)..57 / 100,
        backlundReciprocalKernel u -
          (Set.Iic v).indicator backlundReciprocalKernel u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne v] with u huv
    intro _
    by_cases hu : u ≤ v
    · have hlt : u < v := lt_of_le_of_ne hu huv
      simp [Set.indicator, hu, not_le.mpr hlt]
    · have hge : v ≤ u := le_of_lt (lt_of_not_ge hu)
      simp [Set.indicator, hu, hge]
  rw [he, intervalIntegral.integral_sub
    (kernel_integrable (by norm_num) (by norm_num)) (right_cut_integrable v)]
  rw [show (∫ u in (0 : ℝ)..57 / 100,
      (Set.Iic v).indicator backlundReciprocalKernel u) =
      ∫ u in (0 : ℝ)..v, backlundReciprocalKernel u from
    intervalIntegral.integral_indicator hv]
  rw [kernel_integral (by norm_num), kernel_integral hv.1,
    ← Real.log_div (by norm_num) (by positivity)]
  congr 1
  field_simp
  ring

private theorem right_cut_integral_le {v : ℝ} (hv : 0 ≤ v) :
    (∫ u in (0 : ℝ)..57 / 100,
      (Set.Iic v).indicator backlundReciprocalKernel u) ≤
        Real.log ((3 / 4 + v) / (3 / 4)) := by
  by_cases hb : v ≤ 57 / 100
  · rw [show (∫ u in (0 : ℝ)..57 / 100,
        (Set.Iic v).indicator backlundReciprocalKernel u) =
        ∫ u in (0 : ℝ)..v, backlundReciprocalKernel u from
      intervalIntegral.integral_indicator ⟨hv, hb⟩, kernel_integral hv]
  · have he : (∫ u in (0 : ℝ)..57 / 100,
        (Set.Iic v).indicator backlundReciprocalKernel u) =
        ∫ u in (0 : ℝ)..57 / 100, backlundReciprocalKernel u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      exact Set.indicator_of_mem (by exact le_trans hu.2 (le_of_not_ge hb)) _
    rw [he, kernel_integral (by norm_num)]
    apply Real.log_le_log (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num)

theorem backlund_pair_kernels_integrable (z : ℂ) :
    IntervalIntegrable (fun u => backlundRightKernel z u + backlundLeftKernel z u)
      volume 0 (57 / 100) := by
  have hi := kernel_integrable (by norm_num : (-3 / 4 : ℝ) < 0)
    (by norm_num : (-3 / 4 : ℝ) < 57 / 100)
  have hR : IntervalIntegrable (backlundRightKernel z) volume 0 (57 / 100) := by
    unfold backlundRightKernel
    split_ifs
    · exact right_cut_integrable _
    · exact intervalIntegrable_const
  have hL : IntervalIntegrable (backlundLeftKernel z) volume 0 (57 / 100) := by
    unfold backlundLeftKernel
    split_ifs
    · exact ⟨hi.1.indicator measurableSet_Ici, hi.2.indicator measurableSet_Ici⟩
    · exact intervalIntegrable_const
  exact hR.add hL

private theorem pair_weight_bound {z : ℂ} (hz : z ≠ 0)
    (hr : ‖z‖ ≤ 33 / 25) :
    Real.log (44 / 25 : ℝ) * backlundRightFlag z +
      (∫ u in (0 : ℝ)..57 / 100, backlundRightKernel z u + backlundLeftKernel z u) ≤
        Real.log ((33 / 25 : ℝ) / ‖z‖) +
          if z = (-3 / 4 : ℂ) then Real.log (44 / 25 : ℝ) else 0 := by
  have hw : 0 ≤ Real.log ((33 / 25 : ℝ) / ‖z‖) :=
    Real.log_nonneg ((le_div_iff₀ (norm_pos_iff.mpr hz)).mpr (by simpa using hr))
  by_cases him : z.im = 0
  · have hreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hnorm : ‖z‖ = |z.re| := by
      rw [hreal, Complex.norm_real, Real.norm_eq_abs, ofReal_re]
    have hre : z.re ≠ 0 := by
      intro he
      apply hz
      rw [hreal, he, ofReal_zero]
    by_cases hp : 0 ≤ z.re
    · have hgt : 0 < z.re := lt_of_le_of_ne hp (Ne.symm hre)
      have hc : z ≠ (-3 / 4 : ℂ) := by
        intro he
        have hh := congrArg Complex.re he
        norm_num at hh
        linarith
      simpa [backlundRightFlag, backlundRightKernel, backlundLeftKernel, him,
        not_le.mpr hgt, show ¬z.re ≤ -3 / 4 by linarith, hc] using hw
    · have hneg : z.re < 0 := lt_of_not_ge hp
      rw [abs_of_neg hneg] at hnorm
      by_cases hc : z.re = -3 / 4
      · have he : z = (-3 / 4 : ℂ) := by rw [hreal, hc]; push_cast; rfl
        have hR : (∫ u in (0 : ℝ)..57 / 100,
            (Set.Iic (0 : ℝ)).indicator backlundReciprocalKernel u) = 0 := by
          simpa only [intervalIntegral.integral_same] using!
            (intervalIntegral.integral_indicator (μ := volume)
              (f := backlundReciprocalKernel)
              (show (0 : ℝ) ∈ Set.Icc 0 (57 / 100) by norm_num))
        have hL := left_cut_integral (v := 0) (by norm_num)
        simp only [backlundRightKernel, backlundLeftKernel, him, hc]
        norm_num at hR hL ⊢
        rw [intervalIntegral.integral_add (right_cut_integrable 0)
          (by
            have hi := kernel_integrable (by norm_num : (-3 / 4 : ℝ) < 0)
              (by norm_num : (-3 / 4 : ℝ) < 57 / 100)
            exact ⟨hi.1.indicator measurableSet_Ici, hi.2.indicator measurableSet_Ici⟩),
          hR, hL]
        norm_num [backlundRightFlag, he]
      · by_cases hs : -3 / 4 < z.re
        · have hleft : ¬z.re ≤ -3 / 4 := not_le.mpr hs
          have hcrit : z ≠ (-3 / 4 : ℂ) := by
            intro he
            apply hc
            simpa using congrArg Complex.re he
          have hv : 0 ≤ z.re + 3 / 4 := by linarith
          have hi := right_cut_integral_le hv
          have hprod :
              (44 / 25 : ℝ) * ((3 / 4 + (z.re + 3 / 4)) / (3 / 4)) ≤
                (33 / 25 : ℝ) / (-z.re) := by
            apply (le_div_iff₀ (by linarith : 0 < -z.re)).mpr
            nlinarith [sq_nonneg (z.re + 3 / 4)]
          have hlog := Real.log_le_log (by positivity) hprod
          rw [Real.log_mul (by norm_num) (by positivity)] at hlog
          simp only [backlundRightFlag, backlundRightKernel, backlundLeftKernel, him,
            hneg.le, hleft, Set.mem_Icc, true_and, and_true,
            show -3 / 4 ≤ z.re from hs.le, if_true, if_false, add_zero, mul_one, hcrit]
          rw [hnorm]
          linarith only [hi, hlog]
        · have hlt : z.re < -3 / 4 := lt_of_le_of_ne (le_of_not_gt hs) hc
          have hcrit : z ≠ (-3 / 4 : ℂ) := by
            intro he
            apply hc
            simpa using congrArg Complex.re he
          have hv : -z.re - 3 / 4 ∈ Set.Icc (0 : ℝ) (57 / 100) := by
            rw [hnorm] at hr
            constructor <;> linarith
          have hR : (∫ u in (0 : ℝ)..57 / 100,
              (Set.Iic (z.re + 3 / 4)).indicator backlundReciprocalKernel u) = 0 := by
            calc
              _ = ∫ _u in (0 : ℝ)..57 / 100, (0 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro u hu
                rw [Set.uIcc_of_le (by norm_num)] at hu
                exact Set.indicator_of_notMem
                  (by simp only [Set.mem_Iic]; linarith [hu.1]) _
              _ = 0 := by simp
          have hL := left_cut_integral hv
          have hi := kernel_integrable (by norm_num : (-3 / 4 : ℝ) < 0)
            (by norm_num : (-3 / 4 : ℝ) < 57 / 100)
          simp only [backlundRightFlag, backlundRightKernel, backlundLeftKernel, him,
            hneg.le, hlt.le, Set.mem_Icc, true_and, and_true,
            show ¬-3 / 4 ≤ z.re from not_le.mpr hlt, if_true, if_false,
            mul_zero, zero_add, hcrit]
          rw [intervalIntegral.integral_add (right_cut_integrable _)
            ⟨hi.1.indicator measurableSet_Ici, hi.2.indicator measurableSet_Ici⟩, hR, hL, hnorm]
          have he : 3 / 4 + (-z.re - 3 / 4) = -z.re := by ring
          rw [he]
          simp
  · have hc : z ≠ (-3 / 4 : ℂ) := by
      intro he
      exact him (by simp [he])
    simpa [backlundRightFlag, backlundRightKernel, backlundLeftKernel, him, hc] using hw

theorem backlund_weighted_window_integrals {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) :
    (∑ z ∈ backlundDiskSupport T n,
      (Real.log (44 / 25 : ℝ) * backlundRightFlag z +
        ∫ u in (0 : ℝ)..57 / 100, backlundRightKernel z u + backlundLeftKernel z u)) ≤
      (∑ᶠ z, (divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ)) z : ℝ) *
        Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹)) + Real.log (44 / 25 : ℝ) := by
  classical
  let D := divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ))
  have ha := backlundAux_analyticOnNhd hT n
  have hmem {z : ℂ} (hz : z ∈ backlundDiskSupport T n) : D z ≠ 0 :=
    (D.finiteSupport (isCompact_closedBall ..)).mem_toFinset.mp hz
  have hbound {z : ℂ} (hz : z ∈ backlundDiskSupport T n) :
      Real.log (44 / 25 : ℝ) * backlundRightFlag z +
        (∫ u in (0 : ℝ)..57 / 100, backlundRightKernel z u + backlundLeftKernel z u) ≤
      (D z : ℝ) * Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹) +
        if z = (-3 / 4 : ℂ) then Real.log (44 / 25 : ℝ) else 0 := by
    have hball := D.supportWithinDomain (hmem hz)
    have hnorm : ‖z‖ ≤ 33 / 25 := mem_closedBall_zero_iff.mp hball
    have hzero : z ≠ 0 := by
      intro he
      have h0 : (0 : ℂ) ∈ closedBall 0 (33 / 25 : ℝ) := by norm_num
      have hD0 : D 0 = 0 := by
        simp [D, ha.divisor_apply h0, (ha 0 h0).analyticOrderAt_eq_zero.mpr hn]
      exact hmem hz (by rw [he, hD0])
    have hd : (1 : ℝ) ≤ D z := by
      have hnon : (0 : ℤ) ≤ D z := ha.divisor_nonneg z
      have hne := hmem hz
      exact_mod_cast (by omega : (1 : ℤ) ≤ D z)
    have hw : 0 ≤ Real.log ((33 / 25 : ℝ) / ‖z‖) :=
      Real.log_nonneg ((le_div_iff₀ (norm_pos_iff.mpr hzero)).mpr (by simpa using hnorm))
    have hp := pair_weight_bound hzero hnorm
    simp only [div_eq_mul_inv] at hp hw
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hw]
  have hs := Finset.sum_le_sum (fun z hz => hbound hz)
  simp only [Finset.sum_add_distrib] at hs ⊢
  have hf :
      (∑ z ∈ backlundDiskSupport T n, (D z : ℝ) * Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹)) =
      ∑ᶠ z, (D z : ℝ) * Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹) := by
    symm
    apply finsum_eq_sum_of_support_subset
    intro z hz
    apply (D.finiteSupport (isCompact_closedBall ..)).mem_toFinset.mpr
    have hh := Function.mem_support.mp hz
    exact fun he => hh (by simp [he])
  rw [hf] at hs
  have he : (∑ z ∈ backlundDiskSupport T n,
      if z = (-3 / 4 : ℂ) then Real.log (44 / 25 : ℝ) else 0) ≤
        Real.log (44 / 25 : ℝ) := by
    simp only [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 44 / 25)).le
  exact hs.trans (add_le_add le_rfl he)

#print axioms backlund_pair_kernels_integrable
#print axioms backlund_weighted_window_integrals

end LiuWang.Proof.Campaign20260915.RosserCount
