import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelSmallArc
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsHankelC1 (s : ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  rsHankelArc s m u +
    (∫ y : ℝ in Ioi (Real.exp u), rsHankelLeftBank s m y) -
      ∫ y : ℝ in Ioi (Real.exp u), rsHankelRightBank s m y

theorem rsHankelArc_actual_integral (s : ℂ) (m : ℕ) (u : ℝ) :
    rsHankelArc s m u =
      ∫ θ : ℝ in -(Real.pi / 2)..3 * Real.pi / 2,
        I * exp (u + θ * I) * rsHankelKernel s m (exp (u + θ * I)) := by
  rw [rsHankelArc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro θ hθ
  have hp : -(Real.pi / 2) ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  have ht : -(Real.pi / 2) < θ ∧ θ < 3 * Real.pi / 2 := by
    simpa [uIoo, min_eq_left hp, max_eq_right hp] using hθ
  dsimp only
  rw [rsHankelLift_actual s m (by simpa using ht.1) (by simpa using ht.2)]
  ring

theorem rsHankelArc_actual_integrable (s : ℂ) (m : ℕ) {u : ℝ} (hu : u < 0) :
    IntervalIntegrable (fun θ : ℝ =>
      I * exp (u + θ * I) * rsHankelKernel s m (exp (u + θ * I))) volume
        (-(Real.pi / 2)) (3 * Real.pi / 2) := by
  apply ((rsHankelArc_integrable s m hu).const_mul I).congr_uIoo
  intro θ hθ
  have hp : -(Real.pi / 2) ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  have ht : -(Real.pi / 2) < θ ∧ θ < 3 * Real.pi / 2 := by
    simpa [uIoo, min_eq_left hp, max_eq_right hp] using hθ
  dsimp only
  rw [rsHankelLift_actual s m (by simpa using ht.1) (by simpa using ht.2)]
  ring

theorem rsHankelC1_initial_independent {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re)
    {u v : ℝ} (hu : u < 0) (hv : v < 0) :
    rsHankelC1 s m u = rsHankelC1 s m v := by
  obtain ⟨hr, hl⟩ := rsHankelBanks_integrable hm hs
  have hint (f : ℝ → ℂ) (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
      IntegrableOn (fun y : ℝ => (Real.exp y : ℂ) * f (Real.exp y)) (Ioi x) := by
    simpa only [real_smul, smul_eq_mul] using
      (integrableOn_comp_exp_Ioi f x).mpr
        (hf.mono_set (Ioi_subset_Ioi (Real.exp_pos x).le))
  have he (f : ℝ → ℂ) (hf : IntegrableOn f (Ioi 0)) :
      (∫ x : ℝ in u..v, (Real.exp x : ℂ) * f (Real.exp x)) =
        (∫ y : ℝ in Ioi (Real.exp u), f y) -
          ∫ y : ℝ in Ioi (Real.exp v), f y := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (hint f hf u) (hint f hf v)]
    simpa only [real_smul, smul_eq_mul] using
      congrArg₂ (· - ·) (integral_comp_exp_Ioi f u) (integral_comp_exp_Ioi f v)
  have h := rsHankelArc_difference s m hu hv
  rw [he _ hl, he _ hr] at h
  unfold rsHankelC1
  linear_combination -h

theorem rsHankelC1_initial_actual_banks {m : ℕ} (hm : 0 < m)
    {s : ℂ} (hs : 1 < s.re) {u : ℝ} (hu : u < 0) :
    rsHankelC1 s m u =
      (∫ y : ℝ in Ioi 0, rsHankelLeftBank s m y) -
        ∫ y : ℝ in Ioi 0, rsHankelRightBank s m y := by
  obtain ⟨hr, hl⟩ := rsHankelBanks_integrable hm hs
  have hex : Tendsto Real.exp atBot (𝓝[Ici 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_atBot,
      Eventually.of_forall (fun x => (Real.exp_pos x).le)⟩
  have ht := ((rsHankelArc_tendsto_zero m hs).add
    (hl.continuousWithinAt_Ici_primitive_Ioi.tendsto.comp hex)).sub
      (hr.continuousWithinAt_Ici_primitive_Ioi.tendsto.comp hex)
  rw [zero_add] at ht
  have he : (fun v : ℝ => rsHankelC1 s m u) =ᶠ[atBot] rsHankelC1 s m := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with v hv
    exact rsHankelC1_initial_independent hm hs hu hv
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' he) ht

theorem zeta_eq_sum_add_fixed_hankel {m : ℕ} (hm : 0 < m)
    {s : ℂ} (hs : 1 < s.re) (ht : 0 < s.im) {u : ℝ} (hu : u < 0) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      ((2 * Real.pi : ℂ) ^ s * exp (Real.pi * I * s / 2) /
        (Gamma s * (exp (2 * Real.pi * I * s) - 1))) * rsHankelC1 s m u := by
  rw [rsHankelC1_initial_actual_banks hm hs hu]
  exact zeta_eq_sum_add_hankel_banks m hs ht

end LiuWang.Proof.Campaign20260915.ZetaValidation
