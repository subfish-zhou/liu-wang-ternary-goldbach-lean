import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.Source27Endpoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Original moving endpoint and monotonicity of the analytic antiderivative -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

theorem source27_endpoint_log_identity {L : ℝ} (hL : 1 < L) :
    Real.log (10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ))) =
      Real.log 10000 + 3 * Real.log L + Real.log 3 + Real.log (Real.log L) := by
  have h0 : 0 < L := by linarith
  have hl : 0 < Real.log L := Real.log_pos hL
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0) (pow_pos h0 _).ne',
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hl.ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  ring

theorem source27_scaled_log_endpoint {u : ℝ} (hu : 1 ≤ u) :
    Real.log (10000 * (3100 * u ^ (8 : ℕ)) ^ (3 : ℕ) *
      Real.log ((3100 * u ^ (8 : ℕ)) ^ (3 : ℕ))) ≤ 36.511 * u := by
  have hu0 : 0 < u := by linarith
  have hu8 : 1 ≤ u ^ (8 : ℕ) := one_le_pow₀ hu
  have hL : 1 < 3100 * u ^ (8 : ℕ) := by nlinarith
  have hlog : Real.log (3100 * u ^ (8 : ℕ)) = Real.log 3100 + 8 * Real.log u := by
    rw [Real.log_mul (by norm_num : (3100 : ℝ) ≠ 0) (pow_pos hu0 _).ne', Real.log_pow]
    norm_num
  have hh := Real.log_le_sub_one_of_pos (pow_pos hu0 8)
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hprod := mul_nonneg (show 0 ≤ Real.log (3100 : ℝ) - 1 by linarith [log_3100_bounds.1])
    (sub_nonneg.mpr hu8)
  have hlog1 : Real.log (3100 * u ^ (8 : ℕ)) ≤ Real.log 3100 * u ^ (8 : ℕ) := by
    rw [hlog]
    nlinarith
  have hlog2 := Real.log_le_log (Real.log_pos hL) hlog1
  rw [Real.log_mul (ne_of_gt (by linarith [log_3100_bounds.1] : 0 < Real.log (3100 : ℝ)))
    (pow_pos hu0 _).ne', Real.log_pow] at hlog2
  norm_num only [Nat.cast_ofNat] at hlog2
  rw [hlog] at hlog2
  have hb := source27_log_endpoint
  rw [source27_endpoint_log_identity (by norm_num : (1 : ℝ) < 3100)] at hb
  rw [source27_endpoint_log_identity hL, hlog]
  have huLog := Real.log_le_sub_one_of_pos hu0
  linarith

theorem source27Primitive_nonneg {k s : ℝ} (hk : 0 < k) (hs : 10 ≤ s) :
    0 ≤ source27Primitive k 0.87399 s := by
  have hs0 : 0 ≤ s := by linarith
  have hc : 0 ≤ (0.87399 : ℝ) * Real.pi := by positivity
  have hc4 : (0.87399 : ℝ) * Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
  have h1 : (3 / 5 : ℝ) * s ≤ s - 0.87399 * Real.pi := by linarith
  have h2 : (48 / 5 : ℝ) * s ≤ 12 * s - 6 * 0.87399 * Real.pi := by linarith
  have h1' := mul_le_mul_of_nonneg_right h1 (sq_nonneg k)
  have h2' := mul_le_mul_of_nonneg_right h2 (sq_nonneg s)
  have h3 := mul_nonneg (show 0 ≤ (3 / 5 : ℝ) * s by positivity)
    (sq_nonneg (k - (5 / 2) * s))
  have h4 : 0 ≤ 2 * 0.87399 * Real.pi * k * s := by positivity
  have h5 : 0 ≤ s ^ (3 : ℕ) := by positivity
  have hn : 0 ≤ (s - 0.87399 * Real.pi) * k ^ (2 : ℕ) -
      3 * k * s ^ (2 : ℕ) + 2 * 0.87399 * Real.pi * k * s +
        (12 * s - 6 * 0.87399 * Real.pi) * s ^ (2 : ℕ) := by
    nlinarith only [h1', h2', h3, h4, h5]
  have he : source27Primitive k 0.87399 s =
      s ^ (2 : ℕ) / (Real.pi * k ^ (3 : ℕ)) *
        ((s - 0.87399 * Real.pi) * k ^ (2 : ℕ) -
          3 * k * s ^ (2 : ℕ) + 2 * 0.87399 * Real.pi * k * s +
            (12 * s - 6 * 0.87399 * Real.pi) * s ^ (2 : ℕ)) *
              Real.exp (-k / s) := by
    unfold source27Primitive
    field_simp
    ring
  rw [he]
  exact mul_nonneg (mul_nonneg (by positivity) hn) (Real.exp_pos _).le

theorem source27Primitive_monotone {k : ℝ} (hk : 0 < k) :
    MonotoneOn (source27Primitive k 0.87399) (Set.Ici 10) := by
  have hd (s : ℝ) (hs : s ∈ Set.Ici (10 : ℝ)) :=
    source27Primitive_deriv (c := (0.87399 : ℝ)) hk.ne'
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 10) hs))
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (10 : ℝ))
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
  intro s hs
  have hs10 : 10 ≤ s := interior_subset hs
  have hb : 0 ≤ s / Real.pi - 0.87399 := by
    have hh : (0.87399 : ℝ) ≤ s / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
    linarith
  exact (mul_nonneg hb (Real.exp_pos _).le).trans (source27Primitive_majorizes hk hs10)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
