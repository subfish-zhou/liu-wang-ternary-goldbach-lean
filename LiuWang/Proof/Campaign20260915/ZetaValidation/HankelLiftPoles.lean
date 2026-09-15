import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelBankApproach

set_option autoImplicit false
noncomputable section
open Complex Set Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsLiftNumerator (s : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  exp (s * w - 2 * Real.pi * I * m * exp w)

def rsLiftDenominator (w : ℂ) : ℂ := rsHankelDenominator (exp w)

theorem exp_rsHankelLog {z : ℂ} (hz : z ≠ 0) : exp (rsHankelLog z) = z := by
  rw [rsHankelLog, exp_add, exp_log (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz),
    exp_pi_div_two_mul_I]
  ring_nf
  simp

theorem rsLiftDenominator_zero_iff {w : ℂ}
    (hlo : -(Real.pi / 2) < w.im) (hhi : w.im < 3 * Real.pi / 2) :
    rsLiftDenominator w = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ w = rsHankelLog n := by
  rw [rsLiftDenominator, rsHankelDenominator_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hn0 : n ≠ 0 := by intro he; simp [he] at hn
    refine ⟨n, hn0, ?_⟩
    rw [← hn, rsHankelLog_exp hlo hhi]
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, exp_rsHankelLog (by exact_mod_cast hn)⟩

theorem rsLiftDenominator_deriv (n : ℤ) (hn : n ≠ 0) :
    HasDerivAt rsLiftDenominator (2 * Real.pi * I * n) (rsHankelLog n) := by
  have he : exp (rsHankelLog n) = n := exp_rsHankelLog (by exact_mod_cast hn)
  have hd := rsHankelDenominator_deriv_int n
  rw [← he] at hd
  have h : HasDerivAt (fun w : ℂ => rsHankelDenominator (exp w))
      ((2 * Real.pi * I) * exp (rsHankelLog n)) (rsHankelLog n) :=
    hd.comp (rsHankelLog n) (hasDerivAt_exp _)
  rwa [he] at h

theorem rsLiftNumerator_pole (s : ℂ) (m : ℕ) (n : ℤ) (hn : n ≠ 0) :
    rsLiftNumerator s m (rsHankelLog n) = (n : ℂ) * rsHankelNumerator s m n := by
  have he : exp (rsHankelLog n) = n := exp_rsHankelLog (by exact_mod_cast hn)
  rw [rsLiftNumerator, he, rsHankelNumerator]
  rw [show s * rsHankelLog n - 2 * Real.pi * I * m * n =
    rsHankelLog n + ((s - 1) * rsHankelLog n - 2 * Real.pi * I * m * n) by ring,
    exp_add, he]

theorem rsHankelLift_meromorphic (s : ℂ) (m : ℕ) (w : ℂ) :
    MeromorphicAt (rsHankelLift s m) w := by
  exact (show AnalyticAt ℂ (rsLiftNumerator s m) w by
    unfold rsLiftNumerator; fun_prop).meromorphicAt.div
      (show AnalyticAt ℂ rsLiftDenominator w by
        unfold rsLiftDenominator rsHankelDenominator; fun_prop).meromorphicAt

theorem rsHankelLift_analytic_off (s : ℂ) (m : ℕ) {w : ℂ}
    (hn : rsLiftDenominator w ≠ 0) : AnalyticAt ℂ (rsHankelLift s m) w := by
  exact (show AnalyticAt ℂ (rsLiftNumerator s m) w by
    unfold rsLiftNumerator; fun_prop).div
      (show AnalyticAt ℂ rsLiftDenominator w by
        unfold rsLiftDenominator rsHankelDenominator; fun_prop) hn

theorem rsHankelLift_order_pole (s : ℂ) (m : ℕ) (n : ℤ) (hn : n ≠ 0) :
    meromorphicOrderAt (rsHankelLift s m) (rsHankelLog n) = (-1 : ℤ) := by
  have ha : AnalyticAt ℂ (rsLiftNumerator s m) (rsHankelLog n) := by
    unfold rsLiftNumerator; fun_prop
  have hb : AnalyticAt ℂ rsLiftDenominator (rsHankelLog n) := by
    unfold rsLiftDenominator rsHankelDenominator; fun_prop
  have hzero : rsLiftDenominator (rsHankelLog n) = 0 := by
    rw [rsLiftDenominator, exp_rsHankelLog (by exact_mod_cast hn)]
    exact (rsHankelDenominator_zero_iff _).mpr ⟨n, rfl⟩
  have hder : deriv rsLiftDenominator (rsHankelLog n) ≠ 0 := by
    rw [(rsLiftDenominator_deriv n hn).deriv]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) (by exact_mod_cast hn)
  change meromorphicOrderAt (rsLiftNumerator s m / rsLiftDenominator) _ = _
  rw [meromorphicOrderAt_div ha.meromorphicAt hb.meromorphicAt,
    ha.meromorphicOrderAt_eq, hb.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_zero.mpr (exp_ne_zero _),
    hb.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hder, ENat.map_zero, ENat.map_one]
  rfl

theorem rsHankelLift_residue (s : ℂ) (m : ℕ) (n : ℤ) (hn : n ≠ 0) :
    residue (rsHankelLift s m) (rsHankelLog n) = residue (rsHankelKernel s m) n := by
  have ha : ContinuousAt (rsLiftNumerator s m) (rsHankelLog n) := by
    unfold rsLiftNumerator; fun_prop
  have hzero : rsLiftDenominator (rsHankelLog n) = 0 := by
    rw [rsLiftDenominator, exp_rsHankelLog (by exact_mod_cast hn)]
    exact (rsHankelDenominator_zero_iff _).mpr ⟨n, rfl⟩
  have hc : (2 * Real.pi * I * (n : ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) (by exact_mod_cast hn)
  have h := (ha.tendsto.mono_left nhdsWithin_le_nhds).div
    (rsLiftDenominator_deriv n hn).tendsto_slope hc
  have he : (fun w : ℂ => rsLiftNumerator s m w /
      slope rsLiftDenominator (rsHankelLog n) w) =
      fun w => (w - rsHankelLog n) * rsHankelLift s m w := by
    funext w
    rw [slope_def_field, hzero, sub_zero, div_div_eq_mul_div]
    change rsLiftNumerator s m w * (w - rsHankelLog n) / rsLiftDenominator w =
      (w - rsHankelLog n) * (rsLiftNumerator s m w / rsLiftDenominator w)
    ring
  change Tendsto (fun w => rsLiftNumerator s m w / slope rsLiftDenominator (rsHankelLog n) w) _ _ at h
  rw [he] at h
  rw [residue_eq_of_tendsto h, rsLiftNumerator_pole s m n hn,
    rsHankelKernel_residue s m hn]
  field_simp

end LiuWang.Proof.Campaign20260915.ZetaValidation
