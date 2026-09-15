import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Uniform

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

def cubicMass (delta : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ eta in -delta..delta, ‖f eta‖ ^ 3

theorem cubicMass_nonneg {delta : ℝ} (hd : 0 ≤ delta) (f : ℝ → ℂ) :
    0 ≤ cubicMass delta f :=
  intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)

theorem cubicMass_zero (f : ℝ → ℂ) : cubicMass 0 f = 0 := by
  simp [cubicMass]

theorem continuous_memLp_Ioc {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : Continuous f) (a b : ℝ) (p : ENNReal) :
    MemLp f p (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc a b))
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x ⟨hx.1.le, hx.2⟩

theorem integral_norm_sq_mul_le {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) {delta : ℝ} (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖f eta‖ ^ 2 * ‖g eta‖) ≤
      cubicMass delta f ^ (2 / 3 : ℝ) * cubicMass delta g ^ (1 / 3 : ℝ) := by
  have hp : (3 / 2 : ℝ).HolderConjugate 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Filter.Eventually.of_forall (fun eta => sq_nonneg ‖f eta‖))
    (Filter.Eventually.of_forall (fun eta => norm_nonneg (g eta)))
    (continuous_memLp_Ioc (hf.norm.pow 2) (-delta) delta _)
    (continuous_memLp_Ioc hg.norm (-delta) delta _)
  have he (x : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ (3 / 2 : ℝ) = x ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  simp only [he _ (norm_nonneg _), Real.rpow_ofNat] at h
  simpa only [cubicMass, intervalIntegral.integral_of_le (by linarith : -delta ≤ delta),
    show (1 / (3 / 2) : ℝ) = 2 / 3 by norm_num] using h

theorem norm_integral_sq_mul_phase_le {f g phase : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hp : ∀ eta, ‖phase eta‖ = 1)
    {delta : ℝ} (hd : 0 ≤ delta) :
    ‖∫ eta in -delta..delta, f eta ^ 2 * g eta * phase eta‖ ≤
      cubicMass delta f ^ (2 / 3 : ℝ) * cubicMass delta g ^ (1 / 3 : ℝ) := by
  apply (intervalIntegral.norm_integral_le_integral_norm
    (by linarith : -delta ≤ delta)).trans
  simpa only [norm_mul, norm_pow, hp, mul_one] using
    integral_norm_sq_mul_le hf hg hd

theorem cubicMass_le_const {delta B : ℝ} (hd : 0 ≤ delta)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hb : ∀ eta ∈ Icc (-delta) delta, ‖f eta‖ ≤ B) :
    cubicMass delta f ≤ 2 * delta * B ^ 3 := by
  calc
    _ ≤ ∫ _eta in -delta..delta, B ^ 3 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hf.norm.pow 3).intervalIntegrable _ _) intervalIntegrable_const
      intro eta he
      exact pow_le_pow_left₀ (norm_nonneg _) (hb eta he) 3
    _ = _ := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

theorem integral_J_cubic_sharp {N : ℕ} (hN : 0 < N) :
    (∫ eta : ℝ, ‖J N eta‖ ^ 3) ≤ (2.994003 / Real.pi) * (N : ℝ) ^ 2 := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have ha : 0 < 1 / (Real.pi * (0.999 * (N : ℝ))) := by positivity
  have h := integral_norm_core_tail (cubeIntegrand_integrable hN) ha
    (B := (0.999 * (N : ℝ)) ^ 3) (C := 1 / Real.pi ^ 3)
    (fun eta => by
      simpa only [cubeIntegrand, norm_mul, norm_pow,
        charReal_norm, mul_one] using
        pow_le_pow_left₀ (norm_nonneg _) (J_norm_le_length N eta) 3)
    (fun eta he => cubeIntegrand_norm_le hN (abs_pos.mp (ha.trans he)))
  simp only [cubeIntegrand, norm_mul, norm_pow, charReal_norm, mul_one] at h
  apply h.trans_eq
  field_simp
  ring

theorem cubicMass_J_source {N : ℕ} (hN : 0 < N)
    {delta : ℝ} (hd : 0 ≤ delta) :
    cubicMass delta (J N) ≤ (2.994006 / Real.pi) * (N : ℝ) ^ 2 := by
  have hi : Integrable (fun eta : ℝ => ‖J N eta‖ ^ 3) := by
    simpa only [cubeIntegrand, norm_mul, norm_pow, charReal_norm, mul_one] using
      (cubeIntegrand_integrable hN).norm
  calc
    _ ≤ ∫ eta : ℝ, ‖J N eta‖ ^ 3 := by
      rw [cubicMass, intervalIntegral.integral_of_le (by linarith : -delta ≤ delta)]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => by positivity))
    _ ≤ (2.994003 / Real.pi) * (N : ℝ) ^ 2 := integral_J_cubic_sharp hN
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le

end LiuWang.Proof.SourceRoute.MajorOrdinary
