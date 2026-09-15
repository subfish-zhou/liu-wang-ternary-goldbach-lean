import LiuWang.Proof.SingularIntegral.Convolution
import LiuWang.Proof.SingularIntegral.Region

/-!
# Liu--Wang Lemma 4.1 与 (4.3)

从真实原窗的 Fourier 反演出发，以精确支集等式识别三角域，
最后使用两个一维换元，产生 `N²`。对所有正自然数 `N` 和所有
复参数成立；原文的实部条件是此结论的特例。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Interval Convolution
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SingularIntegral

theorem scaled_window_conditions {N : ℕ} (hN : 0 < N) (s t : ℝ) :
    (s ∈ Icc (sourceWindowLower N) N ∧
      t ∈ Icc (sourceWindowLower N) N ∧
      (N : ℝ) - s - t ∈ Icc (sourceWindowLower N) N) ↔
    (s ∈ Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.998) ∧
      t ∈ Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.999 - s)) := by
  have hp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  simp only [mem_Icc, sourceWindowLower]
  constructor
  · rintro ⟨⟨ha, hb⟩, ⟨hc, hd⟩, he, hf⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      by linarith, by linarith⟩

theorem window_product_eq_triangle_indicator {N : ℕ} (hN : 0 < N)
    (rho₁ rho₂ rho₃ : ℂ) (s t : ℝ) :
    windowWeight N rho₁ s * windowWeight N rho₂ t * windowWeight N rho₃ (N - s - t) =
      (Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.998)).indicator
        (fun s => (Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.999 - s)).indicator
          (fun t => (s : ℂ) ^ (rho₁ - 1) * (t : ℂ) ^ (rho₂ - 1) *
            (((N : ℝ) - s - t : ℝ) : ℂ) ^ (rho₃ - 1)) t) s := by
  have hs := scaled_window_conditions hN s t
  simp only [windowWeight, indicator_apply]
  split_ifs <;> simp_all

theorem tripleConvolution_eq_scaled_triangle {N : ℕ} (hN : 0 < N)
    (rho₁ rho₂ rho₃ : ℂ) :
    tripleConvolution N rho₁ rho₂ rho₃ N =
      ∫ s in ((N : ℝ) * 0.001)..((N : ℝ) * 0.998),
        ∫ t in ((N : ℝ) * 0.001)..((N : ℝ) * 0.999 - s),
          (s : ℂ) ^ (rho₁ - 1) * (t : ℂ) ^ (rho₂ - 1) *
            (((N : ℝ) - s - t : ℝ) : ℂ) ^ (rho₃ - 1) := by
  have hp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  change (∫ s : ℝ, windowWeight N rho₁ s *
    ∫ t : ℝ, windowWeight N rho₂ t * windowWeight N rho₃ ((N : ℝ) - s - t)) = _
  simp_rw [← integral_const_mul, ← mul_assoc, window_product_eq_triangle_indicator hN]
  have hs : ∀ s : ℝ,
      (∫ t : ℝ, (Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.998)).indicator
        (fun s => (Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.999 - s)).indicator
          (fun t => (s : ℂ) ^ (rho₁ - 1) * (t : ℂ) ^ (rho₂ - 1) *
            (((N : ℝ) - s - t : ℝ) : ℂ) ^ (rho₃ - 1)) t) s) =
      (Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.998)).indicator
        (fun s => ∫ t in ((N : ℝ) * 0.001)..((N : ℝ) * 0.999 - s),
          (s : ℂ) ^ (rho₁ - 1) * (t : ℂ) ^ (rho₂ - 1) *
            (((N : ℝ) - s - t : ℝ) : ℂ) ^ (rho₃ - 1)) s := by
    intro s
    by_cases hs : s ∈ Icc ((N : ℝ) * 0.001) ((N : ℝ) * 0.998)
    · simp only [indicator_of_mem hs]
      rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [hs.2])]
    · simp [hs]
  simp_rw [hs]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (N : ℝ) * 0.001 ≤ (N : ℝ) * 0.998)]

theorem integral_Jrho_triple_eq_simplex {N : ℕ} (hN : 0 < N)
    (rho₁ rho₂ rho₃ : ℂ) :
    (∫ eta : ℝ, charReal (-(N : ℝ) * eta) *
      Jrho N rho₁ eta * Jrho N rho₂ eta * Jrho N rho₃ eta) =
      (N : ℂ) ^ 2 * (∫ x₁ in (0.001 : ℝ)..0.998,
        ∫ x₂ in (0.001 : ℝ)..(0.999 - x₁),
          (((N : ℝ) * x₁ : ℝ) : ℂ) ^ (rho₁ - 1) *
          (((N : ℝ) * x₂ : ℝ) : ℂ) ^ (rho₂ - 1) *
          (((N : ℝ) * (1 - x₁ - x₂) : ℝ) : ℂ) ^ (rho₃ - 1)) := by
  rw [integral_Jrho_triple_eq_convolution hN, tripleConvolution_eq_scaled_triangle hN]
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have he : ∀ s : ℝ, (N : ℝ) * 0.999 - s = (N : ℝ) * (0.999 - s / N) := by
    intro s
    field_simp
  simp_rw [he]
  rw [triangle_two_dimensional_scaling]
  simp only [Complex.ofReal_natCast, mul_sub, mul_one]

theorem integral_J_triple {N : ℕ} (hN : 0 < N) :
    (∫ eta : ℝ, charReal (-(N : ℝ) * eta) * J N eta * J N eta * J N eta) =
      (N : ℂ) ^ 2 * ((0.997 : ℂ) ^ 2 / 2) := by
  have h := integral_Jrho_triple_eq_simplex hN 1 1 1
  simpa only [Jrho_one_eq_J, sub_self, Complex.cpow_zero, one_mul,
    triangle_iterated_area_complex] using h

end LiuWang.Proof.SingularIntegral
