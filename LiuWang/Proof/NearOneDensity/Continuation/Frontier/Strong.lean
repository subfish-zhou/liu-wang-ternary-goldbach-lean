import LiuWang.Proof.NearOneDensity.Continuation.Frontier.ActualCount

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.NearOneDensity.Continuation.Frontier

theorem strong_last_zeroCount {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ 0.478) :
    zeroCount q (1 - lam / Real.log z) y ≤ 13800 := by
  have hb := strong_last_budget hlam hupper (source_inverse_log_bounds hz).1
    (source_inverse_log_bounds hz).2 kappa_le_rational
  exact actual_count_of_weight_bound .r0478 (K := 6900) hz hqy hlam hupper
    hb.1 hb.2.1 hb.2.2.2.1 hb.2.2.2.2 (strong_row_weight_mass .r0478 hz)

theorem strong_last_familyCount {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ 0.478) :
    DirichletZeroCount.familyCount q (1 - lam / Real.log z) y ≤ 13800 := by
  rw [familyCount_eq_zeroCount (source_alpha_ge_half hz (by linarith))]
  exact strong_last_zeroCount hz hqy hlam hupper

theorem strong_last_tail {q : ℕ} [NeZero q] {z alpha y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - 0.478 / Real.log z ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ 13800 :=
  (familyCount_antitone_alpha ha).trans
    (strong_last_familyCount hz hqy (by norm_num) le_rfl)

theorem strong_last_inverse_band {q : ℕ} [NeZero q] {z alpha u y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - 0.478 / Real.log z ≤ alpha) (hu : 0 < u) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) / |ρ.im|) ≤ 13800 / u :=
  inverse_band_of_family_bound (strong_last_tail hz hqy ha) hu

end LiuWang.Proof.NearOneDensity.Continuation.Frontier
