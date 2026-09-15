import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ReflectedBudget

set_option autoImplicit false

noncomputable section

open Complex Set Metric
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem reflectedH_jensen {y U r R : ℝ} (hy : 10000 ≤ y) (hr : 0 < r)
    (hrR : r < R) (hRU : R < U) (hR : R ≤ 3 / 2)
    (hwin : |U - y| + R ≤ 3 / 2) :
    ((∑ᶠ s, MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r) s : ℤ) : ℝ) ≤
      Real.log (2 * (1 + windowMajorant y (2 - R)) / ‖reflectedH y U 2‖) /
        Real.log (R / r) := by
  have hRp : 0 < R := hr.trans hrR
  have hA := reflectedH_analytic (y := y) hRU
  have hb := windowMajorant_nonneg hy (2 - R)
  have hJ := AnalyticOnNhd.sum_divisor_le (c := (2 : ℂ))
    (f := reflectedH y U) (r := r) (R := R)
    (M := 2 * (1 + windowMajorant y (2 - R)))
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos hRp] using hrR)
    (by linarith) (by simpa [abs_of_pos hRp] using hA)
    (reflectedH_two_ne_zero (by linarith : 5 ≤ y) U)
    (fun s hs => reflectedH_disk_bound hy hR hwin
      (sphere_subset_closedBall (by simpa [abs_of_pos hRp] using hs)))
  rw [abs_of_pos hr] at hJ
  exact hJ

theorem reflectedH_order_finite {y U R : ℝ} (hy : 5 ≤ y)
    (hR : 0 ≤ R) (hRU : R < U) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) R) :
    analyticOrderAt (reflectedH y U) s ≠ ⊤ := by
  have hA := reflectedH_analytic (y := y) hRU
  have hc : (2 : ℂ) ∈ closedBall (2 : ℂ) R := mem_closedBall_self hR
  apply AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hA
    (convex_closedBall (2 : ℂ) R).isPreconnected hc hs
  rw [(hA 2 hc).analyticOrderAt_eq_zero.mpr (reflectedH_two_ne_zero hy U)]
  simp

theorem reflectedH_divisor_actual_order {y U r R : ℝ} (hy : 5 ≤ y)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hRU : R < U)
    {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) r) :
    MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r) s =
      (analyticOrderNatAt (reflectedH y U) s : ℤ) := by
  have hA := (reflectedH_analytic (y := y) hRU).mono (closedBall_subset_closedBall hrR)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hA hs,
    ← Nat.cast_analyticOrderNatAt (reflectedH_order_finite hy (hr.trans hrR) hRU
      (closedBall_subset_closedBall hrR hs))]
  simp

theorem reflectedH_jensen_explicit {y U r R : ℝ} (hy : 10000 ≤ y) (hr : 0 < r)
    (hrR : r < R) (hRU : R < U) (hR : R ≤ 3 / 2)
    (hwin : |U - y| + R ≤ 3 / 2) :
    ((∑ᶠ s, MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r) s : ℤ) : ℝ) ≤
      Real.log (2 * (1 + windowMajorant y (2 - R)) / (2 - 8 / (y - 1) ^ 2)) /
        Real.log (R / r) := by
  have hq : 8 / (y - 1) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < y - 1))).mpr
    nlinarith
  have hfloor : 0 < 2 - 8 / (y - 1) ^ 2 := by linarith
  have hn := (reflectedH_two_lower (by linarith : 1 < y) U).trans
    (Complex.re_le_norm (reflectedH y U 2))
  have hM : 0 < 2 * (1 + windowMajorant y (2 - R)) := by
    have h := windowMajorant_nonneg hy (2 - R)
    linarith
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  apply (reflectedH_jensen hy hr hrR hRU hR hwin).trans
  apply div_le_div_of_nonneg_right _ hlog.le
  exact Real.log_le_log (div_pos hM (hfloor.trans_le hn))
    (div_le_div_of_nonneg_left hM.le hfloor hn)

theorem actual_source_radii_jensen {y α U : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1)
    (hU : |U - y| ≤ delta y / 4) :
    ((∑ᶠ s, MeromorphicOn.divisor (reflectedH y U)
      (closedBall (2 : ℂ) (2 - α + delta y)) s : ℤ) : ℝ) ≤
      Real.log (2 * (1 + windowMajorant y (α - 3 * delta y / 2)) /
        (2 - 8 / (y - 1) ^ 2)) /
      Real.log ((2 - α + 3 * delta y / 2) / (2 - α + delta y)) := by
  have hd := delta_bounds hy
  have he : 2 - (2 - α + 3 * delta y / 2) = α - 3 * delta y / 2 := by ring
  have h := reflectedH_jensen_explicit (U := U) (r := 2 - α + delta y)
    (R := 2 - α + 3 * delta y / 2) hy
    (by linarith [hd.1]) (by linarith [hd.1])
    (by linarith [abs_le.mp hU, hd.2])
    (by linarith) (by linarith [hd.1])
  rwa [he] at h

theorem actual_reflected_jensen {y U r R : ℝ} (hy : 10000 ≤ y) (hr : 0 < r)
    (hrR : r < R) (hRU : R < U) (hR : R ≤ 3 / 2)
    (hwin : |U - y| + R ≤ 3 / 2) :
    (∀ x : ℝ, reflectedH y U x = 0 ↔ (H y ((x : ℂ) + U * I)).re = 0) ∧
    (∀ s ∈ closedBall (2 : ℂ) r,
      analyticOrderAt (reflectedH y U) s ≠ ⊤ ∧
      MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r) s =
        (analyticOrderNatAt (reflectedH y U) s : ℤ)) ∧
    ((∑ᶠ s, MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r) s : ℤ) : ℝ) ≤
      Real.log (2 * (1 + windowMajorant y (2 - R)) / ‖reflectedH y U 2‖) /
        Real.log (R / r) := by
  refine ⟨fun x => reflectedH_real_zero_iff y U x, ?_, reflectedH_jensen hy hr hrR hRU hR hwin⟩
  intro s hs
  exact ⟨reflectedH_order_finite (by linarith : 5 ≤ y) (hr.trans hrR).le hRU
      (closedBall_subset_closedBall hrR.le hs),
    reflectedH_divisor_actual_order (by linarith) hr.le hrR.le hRU hs⟩

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
