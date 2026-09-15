import LiuWang.Proof.GlobalZeroDensity.Sharp.CriticalBoundary

set_option autoImplicit false

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem actual_mollifier_sharp {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ (64 / 25) * y ∧
      ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        (2583 / 1000) * y + (608 / 1000) * Real.log y + 5608 / 1000 :=
  ⟨norm_Q_sq_le hy t, mollifier_source_bound hy t⟩

theorem actual_detector_lemma_3_2 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) (t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤ 24 * y * (1 + |t|) ∧
      F y ((1 / 2 : ℂ) + t * Complex.I) ≤
        sourceCoefficient t * (1 / 2 + |t|) *
          ((2583 / 1000) * y + (608 / 1000) * Real.log y + 5608 / 1000) :=
  ⟨F_critical_sharp (by linarith [log_six_ge_one]) t, lemma_3_2 hy t⟩

theorem actual_centered_remainder {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : s.re = 1 / 2) :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
      ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1)) (Set.Ioi (N : ℝ)) ∧
      ‖∫ x in Set.Ioi (N : ℝ),
        ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
          (Real.sqrt (N : ℝ))⁻¹ :=
  ⟨centered_remainder_integrable hN hs, centered_remainder_bound hN hs⟩

theorem actual_mollifier_mean (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable (fun t : ℝ => ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2)
      MeasureTheory.volume (-u) u ∧
      (∫ t in -u..u, ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        (2 * u + 4 * (⌈y⌉₊ : ℝ)) * (1 + Real.log ⌈y⌉₊) + 4 * (⌈y⌉₊ : ℝ) :=
  ⟨Q_mean_integrable y u, Q_mean_le y hu⟩

theorem actual_detector_lemma_3_4 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    {u : ℝ} (hu : 0 ≤ u) :
    M y (1 / 2) (y * u) ≤
      (12508 / 1000) * y * (2 + y * u) *
        ((219021 / 100000) * u + 2906 / 1000) * Real.log y ∧
      M y (1 / 2) y ≤ 60 * y ^ 2 * Real.log y :=
  ⟨lemma_3_4 hy hu, M_critical_at_height (by linarith [log_six_ge_one])⟩

theorem actual_critical_strip_boundary {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ 33 * y ^ 2 ∧
      ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ (3303 / 100) * y ^ 2 :=
  ⟨regularG_critical_max (by linarith [log_six_ge_one]) t, critical_boundary_3_37 hy t⟩

end LiuWang.Proof.GlobalZeroDensity.Sharp
