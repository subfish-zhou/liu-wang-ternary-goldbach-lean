import LiuWang.Proof.SourceRoute.Density.EnergyCount

set_option autoImplicit false

noncomputable section

open Complex Set
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans (nonprincipalRatio)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.SourceRoute.Density

theorem regression_empty_families (X a U R alpha T : ℝ) :
    weightedContour 1 X a U = 0 ∧ weightedContour 2 X a U = 0 ∧
    horizontalEnergyCost 1 X a U R = 0 ∧ horizontalEnergyCost 2 X a U R = 0 ∧
    nonprincipalCount 1 alpha T = 0 ∧ nonprincipalCount 2 alpha T = 0 := by simp

theorem regression_source_radius_ratio :
    (1 : ℝ) / 300 ≤ Real.log ((213 / 200) / (53 / 50)) := by
  have h := source_radii_log_lower (xi := 19 / 20) (d := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem regression_source_reflected_count {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 5 ≤ X) (h : ℝ) :
    ((reflectedZeros chi X h (53 / 50)).card : ℝ) ≤
      300 * (Real.log (2 / (2 - 8 / (X - 1) ^ 2)) + diskEnergy chi X h (213 / 200)) := by
  have hn := source_radii_reflected_count hchi hX (h := h) (xi := 19 / 20) (d := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hn
  exact hn

theorem regression_high_alpha_q_three {y : ℝ} (hy : 2 ≤ y) :
    ∃ a ∈ Ioo (93 / 100 : ℝ) (47 / 50), ∃ U ∈ Ioo y (y + 1 / 100),
      (∀ chi ∈ nonprincipalCharacters 3,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi (3 * y) s ≠ 0) ∧
      2 * Real.pi * (1 / 100) * (nonprincipalCount 3 (19 / 20) y : ℝ) ≤
        2 * (pvBudget 3 (3 * y) ⌈3 * y⌉₊ a U +
          nonprincipalRatio 3 * (16 * U / (3 * y - 1) ^ 2) +
          horizontalEnergyCost 3 (3 * y) a U (2 - a + (1 / 100) / 2)) := by
  have hceil : 3 ≤ ⌈3 * y⌉₊ := by
    have hc : (3 : ℝ) ≤ (⌈3 * y⌉₊ : ℝ) :=
      (show (3 : ℝ) ≤ 3 * y by linarith).trans (Nat.le_ceil _)
    exact_mod_cast hc
  have h := produced_closed_count_energy_unnormalized 3
    (X := 3 * y) (alpha := 19 / 20) (T := y) (d := 1 / 100) (e := 1 / 100)
    (by linarith) (M := ⌈3 * y⌉₊) le_rfl hceil
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num)
  have hphi : Nat.totient 3 = 2 := by rw [Nat.totient_prime (by norm_num)]
  norm_num only [hphi, Nat.cast_ofNat] at h
  convert h using 1
  norm_num

theorem regression_closed_left_and_height {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X d : ℝ} (hX : 3 < X) (hd : 0 ≤ d) {z w s : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ t ∈ RectangleBorder z w, H chi X t ≠ 0)
    (hs : s ∈ Rectangle z w) (hz : chi.LFunction s = 0) (hgap : z.re + d = s.re) :
    d * (Interfaces.zeroMultiplicity chi s : ℝ) ≤
      (RectangleIntegral' (weightedKernel (H chi X) z) z w).re := by
  have h := weighted_L_sum_le hchi hX hd hre him hb {s}
    (fun t ht => by
      have ht' : t = s := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hs, hz, hgap.le⟩)
  simpa only [Finset.sum_singleton] using h

end LiuWang.Proof.SourceRoute.Density
