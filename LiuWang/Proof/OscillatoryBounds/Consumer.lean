import LiuWang.Proof.OscillatoryBounds.Transition
import LiuWang.Proof.Parameters.Main

/-!
# 原 `J`、`Jrho` 的具名消费者

原接口的 `N` 是自然数；分析生产者允许任意正实端点。
`η = 0` 不进入倒数分支，`rho.im = 0` 不进入含 `1 / |rho.im|` 的分支。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.OscillatoryBounds

theorem J_intervalIntegrable (N : ℕ) (η : ℝ) :
    IntervalIntegrable (fun t => charReal (η * t)) volume (sourceWindowLower N) N :=
  intervalIntegrable_charReal _ _ _

theorem Jrho_intervalIntegrable {N : ℕ} (hN : 0 < N) (rho : ℂ) (η : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (rho - 1) * charReal (η * t))
      volume (sourceWindowLower N) N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact intervalIntegrable_cpow_charReal (by unfold sourceWindowLower; positivity)
    (by unfold sourceWindowLower; linarith) rho η

theorem J_length (N : ℕ) (η : ℝ) :
    ‖J N η‖ ≤ 0.999 * (N : ℝ) := by
  have h := norm_integral_charReal_le_length
    (a := sourceWindowLower N) (b := N)
    (by unfold sourceWindowLower; linarith [Nat.cast_nonneg (α := ℝ) N]) η
  unfold J
  convert h using 1
  unfold sourceWindowLower
  ring

theorem J_reciprocal (N : ℕ) {η : ℝ} (hη : η ≠ 0) :
    ‖J N η‖ ≤ 1 / (Real.pi * |η|) :=
  norm_integral_charReal_le_reciprocal _ _ hη

theorem J_bound (N : ℕ) (η : ℝ) :
    ‖J N η‖ ≤ if η = 0 then 0.999 * (N : ℝ)
      else min (0.999 * (N : ℝ)) (1 / (Real.pi * |η|)) := by
  split_ifs with hη
  · exact J_length N η
  · exact le_min (J_length N η) (J_reciprocal N hη)

theorem Jrho_weight {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : 0 < rho.re) (η : ℝ) :
    ‖Jrho N rho η‖ ≤
      (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re :=
  norm_integral_cpow_charReal_le_source_weight (by exact_mod_cast hN) hbeta η

theorem Jrho_real_reciprocal {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im = 0) {η : ℝ} (hη : η ≠ 0) :
    ‖Jrho N rho η‖ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |η|) := by
  have hr : (rho.re : ℂ) = rho := by
    apply Complex.ext <;> simp [hgamma]
  unfold Jrho sourceWindowLower
  rw [← hr]
  convert norm_integral_real_cpow_charReal_le
    (a := (N : ℝ) / 1000) (b := N) (beta := rho.re)
    (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N]) hbeta hη using 1
  congr 2
  ring

theorem Jrho_real_bound {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : 0 < rho.re) (hbeta1 : rho.re ≤ 1) (hgamma : rho.im = 0) (η : ℝ) :
    ‖Jrho N rho η‖ ≤
      if η = 0 then (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re
      else min ((1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re)
        ((0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |η|)) := by
  split_ifs with hη
  · exact Jrho_weight hN hbeta η
  · exact le_min (Jrho_weight hN hbeta η) (Jrho_real_reciprocal hN hbeta1 hgamma hη)

theorem Jrho_real_bound_sourceDomain {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {rho : ℂ} (hbeta : 0 < rho.re) (hbeta1 : rho.re ≤ 1)
    (hgamma : rho.im = 0) (η : ℝ) :
    ‖Jrho N rho η‖ ≤
      if η = 0 then (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re
      else min ((1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re)
        ((0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |η|)) :=
  Jrho_real_bound (Parameters.nat_pos_of_exp_le hN) hbeta hbeta1 hgamma η

theorem Jrho_near {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : 0 ≤ rho.re) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hη : |η| ≤ |rho.im| / (10 * Real.pi * (N : ℝ))) :
    ‖Jrho N rho η‖ ≤ 5 * (N : ℝ) ^ rho.re / |rho.im| :=
  norm_integral_cpow_charReal_near (by exact_mod_cast hN) hbeta hgamma hη

theorem Jrho_sqrt {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) (η : ℝ) :
    ‖Jrho N rho η‖ ≤
      16 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im| :=
  norm_integral_cpow_charReal_sqrt (by exact_mod_cast hN) hbeta hgamma η

theorem Jrho_transition {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) {η : ℝ}
    (_hlo : |rho.im| / (10 * Real.pi * (N : ℝ)) ≤ |η|)
    (_hhi : |η| ≤ |rho.im| / (0.001 * Real.pi * (N : ℝ))) :
    ‖Jrho N rho η‖ ≤
      16 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im| :=
  Jrho_sqrt hN hbeta hgamma η

theorem Jrho_far {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hη : |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |η|) :
    ‖Jrho N rho η‖ ≤ (4 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |η| :=
  norm_integral_cpow_charReal_far (by exact_mod_cast hN) hbeta hgamma hη

theorem Jrho_intervalIntegrable_sourceDomain {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (rho : ℂ) (η : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (rho - 1) * charReal (η * t))
      volume (sourceWindowLower N) N :=
  Jrho_intervalIntegrable (Parameters.nat_pos_of_exp_le hN) rho η

theorem Jrho_near_sourceDomain {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) {rho : ℂ}
    (hbeta : 0 ≤ rho.re) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hη : |η| ≤ |rho.im| / (10 * Real.pi * (N : ℝ))) :
    ‖Jrho N rho η‖ ≤ 5 * (N : ℝ) ^ rho.re / |rho.im| :=
  Jrho_near (Parameters.nat_pos_of_exp_le hN) hbeta hgamma hη

theorem Jrho_transition_sourceDomain {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {rho : ℂ} (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hlo : |rho.im| / (10 * Real.pi * (N : ℝ)) ≤ |η|)
    (hhi : |η| ≤ |rho.im| / (0.001 * Real.pi * (N : ℝ))) :
    ‖Jrho N rho η‖ ≤
      16 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im| :=
  Jrho_transition (Parameters.nat_pos_of_exp_le hN) hbeta hgamma hlo hhi

theorem Jrho_far_sourceDomain {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hη : |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |η|) :
    ‖Jrho N rho η‖ ≤ (4 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |η| :=
  Jrho_far (Parameters.nat_pos_of_exp_le hN) hbeta hgamma hη

end LiuWang.Proof.OscillatoryBounds
