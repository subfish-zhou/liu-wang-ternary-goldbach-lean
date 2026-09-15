import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.Source27Geometry
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.PowerDecay

/-! # Uniform payment of the literal (2.27) scalar integral for every real L >= 3100 -/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

def source27Decay (u : ℝ) : ℝ :=
  signedDecay (0.478 * 3100 / 36.511)
    (0.87399 * Real.pi / 36.511)
    (3 * 36.511 / (0.478 * 3100))
    (6 * 0.87399 * Real.pi * 36.511 / (0.478 * 3100) ^ (2 : ℕ))
    (2 * 0.87399 * Real.pi / (0.478 * 3100))
    (12 * 36.511 ^ (2 : ℕ) / (0.478 * 3100) ^ (2 : ℕ)) u

theorem source27Decay_antitone : AntitoneOn source27Decay (Set.Ici 1) := by
  apply signedDecay_antitone (by norm_num) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)
  norm_num
  linarith [Real.pi_lt_four]

theorem source27_scaled_identity {u : ℝ} (hu : 0 < u) :
    (3100 * u ^ (8 : ℕ)) ^ (4 : ℕ) *
      source27Primitive (0.478 * (3100 * u ^ (8 : ℕ))) 0.87399 (36.511 * u) =
      ((3100 : ℝ) ^ (4 : ℕ) * 36.511 ^ (3 : ℕ) / (Real.pi * (0.478 * 3100))) *
        source27Decay u := by
  have he : -(0.478 * (3100 * u ^ (8 : ℕ))) / (36.511 * u) =
      -(0.478 * 3100 / 36.511) * u ^ (7 : ℕ) := by
    field_simp
  unfold source27Primitive source27Decay signedDecay decayPower
  rw [he]
  field_simp
  ring

theorem source27_scaled_endpoint_le {u : ℝ} (hu : 1 ≤ u) :
    (3100 * u ^ (8 : ℕ)) ^ (4 : ℕ) *
      source27Primitive (0.478 * (3100 * u ^ (8 : ℕ))) 0.87399 (36.511 * u) ≤
      (3100 : ℝ) ^ (4 : ℕ) * source27Primitive (0.478 * 3100) 0.87399 36.511 := by
  have hh := mul_le_mul_of_nonneg_left
    (source27Decay_antitone (show (1 : ℝ) ∈ Set.Ici 1 by norm_num) hu hu)
    (show 0 ≤ (3100 : ℝ) ^ (4 : ℕ) * 36.511 ^ (3 : ℕ) /
      (Real.pi * (0.478 * 3100)) by positivity)
  rw [← source27_scaled_identity (by linarith : 0 < u),
    ← source27_scaled_identity (by norm_num : (0 : ℝ) < 1)] at hh
  simpa only [one_pow, mul_one] using hh

theorem source27_scaled_payment {u : ℝ} (hu : 1 ≤ u) :
    (∫ s in Real.log (3.36 * (3100 * u ^ (8 : ℕ)) ^ (3 : ℕ))..
      Real.log (10000 * (3100 * u ^ (8 : ℕ)) ^ (3 : ℕ) *
        Real.log ((3100 * u ^ (8 : ℕ)) ^ (3 : ℕ))),
          source27Integrand (3100 * u ^ (8 : ℕ)) s) ≤ 0.00197 := by
  have hu8 : 1 ≤ u ^ (8 : ℕ) := one_le_pow₀ hu
  have hL : 3100 ≤ 3100 * u ^ (8 : ℕ) := by nlinarith
  have hk : 0 < 0.478 * (3100 * u ^ (8 : ℕ)) := by positivity
  have hend := source27_original_endpoints hL
  have hA := source27Primitive_nonneg hk hend.1
  have hB := source27Primitive_monotone hk (hend.1.trans hend.2)
    (show 10 ≤ 36.511 * u by linarith) (source27_scaled_log_endpoint hu)
  have h := mul_le_mul_of_nonneg_left hB
    (show 0 ≤ (3100 * u ^ (8 : ℕ)) ^ (4 : ℕ) by positivity)
  have h0 := mul_nonneg (show 0 ≤ (3100 * u ^ (8 : ℕ)) ^ (4 : ℕ) by positivity) hA
  have h1 := original_source27_analytic hL
  have h2 := source27_scaled_endpoint_le hu
  linarith [source27_endpoint_certificate]

theorem original_source27_payment {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ (3 : ℕ))..
      Real.log (10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ))),
        L ^ (4 : ℕ) *
          (s / Real.pi - 0.874 + (6.8423 / 7) * (1 / 100000) * s * Real.exp (-s) +
            (15 / 7) * (1 / 100000) * Real.exp (-s)) *
          Real.exp (-0.478 * L / s)) ≤ 0.00197 := by
  let u : ℝ := (L / 3100) ^ (1 / 8 : ℝ)
  have hr : 1 ≤ L / 3100 := by linarith
  have hu : 1 ≤ u := Real.one_le_rpow hr (by norm_num)
  have hu8 : u ^ (8 : ℕ) = L / 3100 := by
    dsimp only [u]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ L / 3100)]
    norm_num
  have he : L = 3100 * u ^ (8 : ℕ) := by rw [hu8]; ring
  change (∫ s in Real.log (3.36 * L ^ (3 : ℕ))..
    Real.log (10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ))), source27Integrand L s) ≤ _
  rw [he]
  exact source27_scaled_payment hu

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
