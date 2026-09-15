import LiuWang.Proof.NearOneDensity.Continuation.Frontier.JointMass

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.NearOneDensity.Continuation.Frontier

theorem joint_last_zeroCount {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ 0.478) :
    zeroCount q (1 - lam / Real.log z) y ≤ 13000 := by
  have hb := joint_last_budget hlam hupper (source_inverse_log_bounds hz).1
    (source_inverse_log_bounds hz).2 kappa_le_rational
  exact actual_count_of_weight_bound .r0478 (K := 6500) hz hqy hlam hupper
    hb.1 hb.2.1 hb.2.2.2.1 hb.2.2.2.2 (joint_last_weight_mass hz)

theorem joint_last_familyCount {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ 0.478) :
    DirichletZeroCount.familyCount q (1 - lam / Real.log z) y ≤ 13000 := by
  rw [familyCount_eq_zeroCount (source_alpha_ge_half hz (by linarith))]
  exact joint_last_zeroCount hz hqy hlam hupper

theorem joint_last_tail {q : ℕ} [NeZero q] {z alpha y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - 0.478 / Real.log z ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ 13000 :=
  (familyCount_antitone_alpha ha).trans
    (joint_last_familyCount hz hqy (by norm_num) le_rfl)

theorem joint_last_inverse_band {q : ℕ} [NeZero q] {z alpha u y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - 0.478 / Real.log z ≤ alpha) (hu : 0 < u) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) / |ρ.im|) ≤ 13000 / u :=
  inverse_band_of_family_bound (joint_last_tail hz hqy ha) hu

theorem joint_last_complete_count {q : ℕ} [NeZero q] {z alpha y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - 0.478 / Real.log z ≤ alpha) :
    (∑ χ : DirichletCharacter ℂ q,
      ∑ ρ ∈ (CompleteExpansion.zeroValues χ y).filter (fun ρ => alpha ≤ ρ.re),
        analyticOrderNatAt χ.LFunction ρ) ≤ 13000 := by
  have hhalf : 1 / 2 ≤ alpha := (source_alpha_ge_half hz (by norm_num : (0.478 : ℝ) ≤ 0.5)).trans ha
  rw [← DirichletZeroCount.Applications.familyCount_eq_complete_filter q hhalf]
  exact joint_last_tail hz hqy ha

theorem joint_last_low_height {q : ℕ} [NeZero q] {x alpha : ℝ}
    (hx : 100000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (ha : 1 - 0.478 / Real.log x ≤ alpha) :
    DirichletZeroCount.familyCount q alpha (x / q) ≤ 13000 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  apply joint_last_tail hx _ ha
  rw [max_eq_right ((le_div_iff₀ hq0).mpr (by simpa using hq))]
  exact le_of_eq (mul_div_cancel₀ x hq0.ne')

end LiuWang.Proof.NearOneDensity.Continuation.Frontier
