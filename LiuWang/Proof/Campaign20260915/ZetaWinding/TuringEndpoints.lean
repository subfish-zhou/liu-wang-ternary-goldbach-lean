import LiuWang.Proof.Campaign20260915.ZetaWinding.RightLogTail

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.DirichletZeroCount

def turingS (t : ℝ) : ℝ :=
  positiveCount t - 1 - criticalGammaArgument t / Real.pi

def turingSLeft (t : ℝ) : ℝ :=
  positiveCountLeft t - 1 - criticalGammaArgument t / Real.pi

def turingSMid (t : ℝ) : ℝ := (turingS t + turingSLeft t) / 2

theorem finite_left_clearance (F : Finset ℝ) (T : ℝ) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ F, x < T → x ≤ T - e := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x F hx ih =>
    obtain ⟨e, he, hf⟩ := ih
    by_cases hxt : x < T
    · refine ⟨min e (T - x), lt_min he (sub_pos.mpr hxt), ?_⟩
      intro y hy hyt
      rcases Finset.mem_insert.mp hy with rfl | hy
      · linarith [min_le_right e (T - y)]
      · linarith [hf y hy hyt, min_le_left e (T - x)]
    · refine ⟨e, he, ?_⟩
      intro y hy hyt
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hxt hyt).elim
      · exact hf y hy hyt

theorem positiveCount_left_plateau (T : ℝ) :
    ∃ e : ℝ, 0 < e ∧ ∀ u : ℝ, T - e ≤ u → u < T →
      positiveCount u = positiveCountLeft T := by
  classical
  obtain ⟨e, he, hg⟩ := finite_left_clearance ((positiveValues T).image Complex.im) T
  refine ⟨e, he, ?_⟩
  intro u hu huT
  have hv : positiveValues u = (positiveValues T).filter (fun z => z.im < T) := by
    ext z
    rw [Finset.mem_filter, mem_positiveValues, mem_positiveValues]
    constructor
    · rintro ⟨hz, h0, h1, hp, ht⟩
      exact ⟨⟨hz, h0, h1, hp, ht.trans huT.le⟩, ht.trans_lt huT⟩
    · rintro ⟨⟨hz, h0, h1, hp, ht⟩, hlt⟩
      have hm : z.im ∈ (positiveValues T).image Complex.im :=
        Finset.mem_image.mpr ⟨z, mem_positiveValues.mpr ⟨hz, h0, h1, hp, ht⟩, rfl⟩
      exact ⟨hz, h0, h1, hp, (hg z.im hm hlt).trans hu⟩
  simp only [positiveCount, positiveCountLeft, hv]

theorem positiveCount_tendsto_left (T : ℝ) :
    Tendsto (fun u => (positiveCount u : ℝ)) (𝓝[<] T) (𝓝 (positiveCountLeft T : ℝ)) := by
  obtain ⟨e, he, hg⟩ := positiveCount_left_plateau T
  have hnear : ∀ᶠ u : ℝ in 𝓝[<] T, T - e < u :=
    (eventually_gt_nhds (sub_lt_self T he)).filter_mono nhdsWithin_le_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [hnear, self_mem_nhdsWithin] with u hu hut
  exact (congrArg (fun n : ℕ => (n : ℝ)) (hg u hu.le hut)).symm

theorem criticalGammaArgument_continuous : Continuous criticalGammaArgument := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : ContinuousAt (fun u : ℝ => criticalPoint u / 2) t := by
    have he : (fun u : ℝ => criticalPoint u / 2) =
        (fun u : ℝ => ((1 / 2 : ℂ) + (u : ℂ) * I) / 2) := by
      funext u
      congr 1
      apply Complex.ext <;> simp [criticalPoint]
    rw [he]
    fun_prop
  have hg : ContinuousAt gammaLogBranch (criticalPoint t / 2) := by
    exact (Remainder.logGamma_hasDerivAt
      (z := criticalPoint t / 2) (by norm_num [criticalPoint])).continuousAt
  have hh : ContinuousAt (fun u : ℝ => gammaLogBranch (criticalPoint u / 2) -
      criticalPoint u / 2 * (Real.log Real.pi : ℂ)) t :=
    (hg.comp (f := fun u : ℝ => criticalPoint u / 2) hc).sub (hc.mul continuousAt_const)
  exact Complex.continuous_im.continuousAt.comp hh

theorem turingS_tendsto_left (T : ℝ) :
    Tendsto turingS (𝓝[<] T) (𝓝 (turingSLeft T)) :=
  ((positiveCount_tendsto_left T).sub tendsto_const_nhds).sub
    ((criticalGammaArgument_continuous.tendsto T).mono_left nhdsWithin_le_nhds |>.div_const _)

theorem turingS_right_continuous (T : ℝ) :
    ContinuousWithinAt turingS (Set.Ici T) T :=
  ((positiveCount_right_continuous T).sub continuousWithinAt_const).sub
    (criticalGammaArgument_continuous.continuousAt.continuousWithinAt.div_const _)

theorem turingS_jump (T : ℝ) :
    turingS T - turingSLeft T = boundaryMultiplicity T := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (positiveCount_jump T)
  push_cast at h
  dsimp [turingS, turingSLeft]
  linarith

theorem turingS_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable turingS volume a b :=
  ((positiveCount_intervalIntegrable a b).sub intervalIntegrable_const).sub
    ((criticalGammaArgument_continuous.intervalIntegrable a b).div_const _)

theorem turingS_eq_mid_ae_on_interval (a b : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.uIoc a b → turingS t = turingSMid t := by
  classical
  let F := (zetaClosedValues (max a b)).image Complex.im
  filter_upwards [F.finite_toSet.countable.ae_notMem volume] with t ht htI
  have htmax : t ≤ max a b := htI.2
  have hb : boundaryMultiplicity t = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
    have hz' := mem_positiveValues.mp hz
    have hm : z ∈ zetaClosedValues (max a b) :=
      mem_zetaClosedValues.mpr ⟨hz'.1, hz'.2.1, hz'.2.2.1,
        by rw [abs_of_pos hz'.2.2.2.1]; exact hz'.2.2.2.2.trans htmax⟩
    exact (ht (Finset.mem_image.mpr ⟨z, hm, he⟩)).elim
  have hj := turingS_jump t
  rw [hb, Nat.cast_zero] at hj
  dsimp [turingSMid]
  linarith

theorem integral_turingS_eq_mid (a b : ℝ) :
    (∫ t in a..b, turingS t) = ∫ t in a..b, turingSMid t :=
  intervalIntegral.integral_congr_ae (turingS_eq_mid_ae_on_interval a b)

#print axioms positiveCount_tendsto_left
#print axioms turingS_jump
#print axioms turingS_intervalIntegrable
#print axioms integral_turingS_eq_mid

end LiuWang.Proof.Campaign20260915.ZetaWinding
