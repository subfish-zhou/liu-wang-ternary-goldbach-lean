import LiuWang.Proof.SourceRoute.MajorException.Continuation.ConductorMonotone

set_option autoImplicit false
noncomputable section
open Set

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

theorem attenuation_sixteen_upper : attenuation 16 ≤ (1/262144 : ℝ) := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.5)
    (show (2.5 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 8
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have he : attenuation 16 = 1/(Real.exp 8*256) := by
    dsimp [attenuation]
    norm_num
    rw [show (-8 : ℝ) = -(8 : ℝ) by rfl, Real.exp_neg]
    ring
  rw [he]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

theorem profileLogDerivative_sixteen_neg (j : PureKind) :
    profileLogDerivative j 3100 16 < 0 := by
  have hratio := logNuD_ratio_upper (t := 16) (by norm_num)
  have hprod := mul_le_mul (zeroScale_3100_bounds j).2 attenuation_sixteen_upper
    (show 0 ≤ attenuation 16 by dsimp [attenuation]; positivity) (by norm_num)
  have hs : attenuationSlope 16 = (5/8 : ℝ) := by norm_num [attenuationSlope]
  have hp : (1/2 : ℝ) ≤ decayPower j := by cases j <;> norm_num [decayPower]
  dsimp [profileLogDerivative]
  rw [hs, mul_div_assoc]
  nlinarith

theorem critical_point_unique (j : PureKind) :
    ∃! c : ℝ, c ∈ Ioo 8 16 ∧ profileLogDerivative j 3100 c = 0 := by
  have h8 := profileLogDerivative_initial_pos j (t := 8) (by norm_num) le_rfl
  have h16 := profileLogDerivative_sixteen_neg j
  have hc : ContinuousOn (profileLogDerivative j 3100) (Icc 8 16) := by
    intro t ht
    exact (profileLogDerivative_hasDerivAt j 3100 (by have := ht.1; linarith)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hz⟩ := intermediate_value_Icc' (by norm_num : (8 : ℝ) ≤ 16) hc
    (show (0 : ℝ) ∈ Icc (profileLogDerivative j 3100 16)
      (profileLogDerivative j 3100 8) from ⟨h16.le, h8.le⟩)
  have hci : c ∈ Ioo 8 16 := by
    constructor
    · by_contra h
      have : c = 8 := by have := hc.1; linarith
      subst c
      linarith
    · by_contra h
      have : c = 16 := by have := hc.2; linarith
      subst c
      linarith
  refine ⟨c, ⟨hci, hz⟩, ?_⟩
  intro d hd
  exact (profileLogDerivative_strictAnti j (by norm_num : (0 : ℝ) < 3100)).injOn
    hd.1.1.le hc.1 (hd.2.trans hz.symm)

theorem profile_increases_to_critical (j : PureKind) {c : ℝ}
    (hc : c ∈ Ioo 8 16) (hz : profileLogDerivative j 3100 c = 0) :
    StrictMonoOn (conductorProfile j 3100) (Icc 6 c) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 6 c)
  · intro t ht
    exact (profile_hasDerivAt j 3100 (by have := ht.1; linarith)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc, mem_Ioo] at ht
    have hdt : 0 < profileLogDerivative j 3100 t := by
      by_cases ht8 : t ≤ 8
      · exact profileLogDerivative_initial_pos j ht.1.le ht8
      · have h := profileLogDerivative_strictAnti j (by norm_num : (0 : ℝ) < 3100)
          (show t ∈ Ici 8 by exact le_of_not_ge ht8) hc.1.le ht.2
        rwa [hz] at h
    rw [(profile_hasDerivAt j 3100 (by linarith : 1 < t)).deriv]
    exact mul_pos hdt (profile_pos j 3100 (by linarith))

theorem profile_decreases_from_critical (j : PureKind) {c : ℝ}
    (hc : c ∈ Ioo 8 16) (hz : profileLogDerivative j 3100 c = 0) :
    StrictAntiOn (conductorProfile j 3100) (Ici c) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici c)
  · intro t ht
    exact (profile_hasDerivAt j 3100 (by have := hc.1; change c ≤ t at ht; linarith)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    have ht8 : 8 ≤ t := by have := hc.1; linarith
    have hdt := profileLogDerivative_strictAnti j (by norm_num : (0 : ℝ) < 3100)
      hc.1.le ht8 ht
    rw [hz] at hdt
    rw [(profile_hasDerivAt j 3100 (by linarith : 1 < t)).deriv]
    exact mul_neg_of_neg_of_pos hdt (profile_pos j 3100 (by linarith))

theorem profile_global_maximum (j : PureKind) {c : ℝ}
    (hc : c ∈ Ioo 8 16) (hz : profileLogDerivative j 3100 c = 0)
    {t : ℝ} (ht : 6 ≤ t) :
    conductorProfile j 3100 t ≤ conductorProfile j 3100 c := by
  by_cases htc : t ≤ c
  · exact (profile_increases_to_critical j hc hz).monotoneOn ⟨ht, htc⟩
      ⟨by have := hc.1; linarith, le_rfl⟩ htc
  · have hct : c ≤ t := le_of_not_ge htc
    exact (profile_decreases_from_critical j hc hz).antitoneOn
      (mem_Ici.mpr (le_refl c)) (mem_Ici.mpr hct) hct

theorem scalar_critical_reduction (j : PureKind) {c : ℝ}
    (hc : c ∈ Ioo 8 16) (hz : profileLogDerivative j 3100 c = 0)
    {r L : ℝ} (hr : 987 ≤ r) (hL : 3100 ≤ L) :
    conductorScalar j r L ≤ conductorProfile j 3100 c := by
  have hr0 : 0 < r := by linarith
  have ht : 6 ≤ Real.log r :=
    log987_bounds.1.trans (Real.log_le_log (by norm_num) hr)
  calc
    _ ≤ conductorScalar j r 3100 := scalar_antitone_L j (by linarith) hL
    _ = conductorProfile j 3100 (Real.log r) := scalar_eq_profile j hr0 3100
    _ ≤ _ := profile_global_maximum j hc hz ht

theorem critical_point_in_paperDomain {c : ℝ} (hc : c ∈ Ioo 8 16) :
    paperDomain (Real.exp c) 3100 := by
  refine ⟨?_, le_rfl, ?_⟩
  · have h := Real.exp_le_exp.mpr (log987_bounds.2.trans hc.1.le)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 987)] using h
  · have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 16
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    have he := Real.exp_le_exp.mpr hc.2.le
    nlinarith

theorem paper_scalar_maximum (j : PureKind) :
    ∃ c ∈ Ioo (8 : ℝ) 16, profileLogDerivative j 3100 c = 0 ∧
      paperDomain (Real.exp c) 3100 ∧
      conductorScalar j (Real.exp c) 3100 = conductorProfile j 3100 c ∧
      ∀ r L, paperDomain r L →
        conductorScalar j r L ≤ conductorProfile j 3100 c := by
  obtain ⟨c, ⟨hc, hz⟩, _⟩ := critical_point_unique j
  refine ⟨c, hc, hz, critical_point_in_paperDomain hc, ?_, ?_⟩
  · rw [scalar_eq_profile j (Real.exp_pos c), Real.log_exp]
  · intro r L h
    exact scalar_critical_reduction j hc hz h.1 h.2.1

def criticalPoint (j : PureKind) : ℝ := Classical.choose (critical_point_unique j)

theorem criticalPoint_spec (j : PureKind) :
    criticalPoint j ∈ Ioo (8 : ℝ) 16 ∧
      profileLogDerivative j 3100 (criticalPoint j) = 0 :=
  (Classical.choose_spec (critical_point_unique j)).1

def criticalValue (j : PureKind) : ℝ := conductorProfile j 3100 (criticalPoint j)

def sourceScalarBudget : PureKind → ℝ
  | .linear => 0.0000025636
  | .quadratic => 0.00013
  | .cubic => 0.028

theorem original_scalar_bound_iff (j : PureKind) :
    (∀ r L, paperDomain r L → conductorScalar j r L ≤ sourceScalarBudget j) ↔
      criticalValue j ≤ sourceScalarBudget j := by
  have hc := criticalPoint_spec j
  constructor
  · intro h
    have hh := h (Real.exp (criticalPoint j)) 3100 (critical_point_in_paperDomain hc.1)
    rwa [scalar_eq_profile j (Real.exp_pos _), Real.log_exp] at hh
  · intro h r L hd
    exact (scalar_critical_reduction j hc.1 hc.2 hd.1 hd.2.1).trans h

end LiuWang.Proof.SourceRoute.MajorException.Continuation
