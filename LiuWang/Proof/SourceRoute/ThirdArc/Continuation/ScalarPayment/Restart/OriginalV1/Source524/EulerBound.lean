import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Expression
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

private def logCorrection (u : ℝ) : ℝ :=
  Real.log (1 + u) - u / (2 * (1 + u)) - u / 2 + u ^ 2 / 12 -
    u ^ 2 / (12 * (1 + u) ^ 2)

private theorem logCorrection_deriv {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt logCorrection (u ^ 4 / (6 * (1 + u) ^ 3)) u := by
  have hu0 : 1 + u ≠ 0 := by linarith
  have h1 := (hasDerivAt_id u).const_add 1
  have h := (((h1.log hu0).sub
    ((hasDerivAt_id u).div (h1.const_mul 2) (by positivity))).sub
    ((hasDerivAt_id u).div_const 2)).add (((hasDerivAt_id u).pow 2).div_const 12)
  have h := h.sub (((hasDerivAt_id u).pow 2).div
    ((h1.pow 2).const_mul 12) (by
      simpa only [Pi.pow_apply, id_eq] using
        mul_ne_zero (by norm_num : (12 : ℝ) ≠ 0) (pow_ne_zero 2 hu0)))
  simp only [Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  norm_num only [Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) from rfl, pow_one]
  field_simp
  ring

theorem logarithm_correction_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.log (1 + u) - u / (2 * (1 + u)) - u / 2 + u ^ 2 / 12 -
      u ^ 2 / (12 * (1 + u) ^ 2) := by
  have hm : MonotoneOn logCorrection (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun u hu => (logCorrection_deriv hu).continuousAt.continuousWithinAt)
      (fun u hu => (logCorrection_deriv (interior_subset hu)).hasDerivWithinAt)
    intro u hu
    have hu0 : 0 ≤ u := interior_subset hu
    positivity
  have h := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hu hu
  simpa [logCorrection] using h

private def correctedHarmonic (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - 1 / (2 * n) + 1 / (12 * (n : ℝ) ^ 2)

private theorem correctedHarmonic_antitone :
    AntitoneOn correctedHarmonic (Set.Ici 1) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := logarithm_correction_nonneg (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  have hl : Real.log (1 + (n : ℝ)⁻¹) = Real.log ((n : ℝ) + 1) - Real.log n := by
    rw [← Real.log_div (by positivity : (n : ℝ) + 1 ≠ 0) hn0.ne']
    congr 1
    field_simp
  rw [hl] at h
  dsimp only [correctedHarmonic]
  rw [harmonic_succ]
  push_cast
  have heq : (harmonic n : ℝ) + ((n : ℝ) + 1)⁻¹ - Real.log ((n : ℝ) + 1) -
      1 / (2 * ((n : ℝ) + 1)) + 1 / (12 * ((n : ℝ) + 1) ^ 2) -
      ((harmonic n : ℝ) - Real.log n - 1 / (2 * n) + 1 / (12 * (n : ℝ) ^ 2)) =
      -(Real.log ((n : ℝ) + 1) - Real.log n - (n : ℝ)⁻¹ / (2 * (1 + (n : ℝ)⁻¹)) -
        (n : ℝ)⁻¹ / 2 + ((n : ℝ)⁻¹) ^ 2 / 12 -
        ((n : ℝ)⁻¹) ^ 2 / (12 * (1 + (n : ℝ)⁻¹) ^ 2)) := by
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hni : 1 + (n : ℝ)⁻¹ ≠ 0 := by positivity
    field_simp
    ring
  linarith only [heq, h]

theorem euler_corrected_harmonic_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant ≤
      (harmonic n : ℝ) - Real.log n - 1 / (2 * n) + 1 / (12 * (n : ℝ) ^ 2) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto correctedHarmonic atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h := (Real.tendsto_harmonic_sub_log.sub (hi.div_const 2)).add ((hi.pow 2).div_const 12)
    convert h using 1
    · ext n
      dsimp only [correctedHarmonic]
      ring
    · simp
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop n] with m hm
  exact correctedHarmonic_antitone hn (hn.trans hm) hm

theorem euler_upper : Real.eulerMascheroniConstant ≤ (0.577216 : ℝ) := by
  have hl : (0.69314718 : ℝ) ≤ Real.log 2 := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mpr
    have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.69314718)
      (by norm_num : (0.69314718 : ℝ) ≤ 1) (by norm_num : (0 : ℕ) < 13)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith only [h]
  have h := euler_corrected_harmonic_upper (by norm_num : (1 : ℕ) ≤ 16)
  norm_num at h
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at h
  norm_num at h
  linarith

theorem exp_euler_upper : Real.exp Real.eulerMascheroniConstant ≤ (1.781074 : ℝ) := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.577216)
    (by norm_num : (0.577216 : ℝ) ≤ 1) (by norm_num : (0 : ℕ) < 12)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  exact (Real.exp_le_exp.mpr euler_upper).trans (by linarith only [h])

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
