import LiuWang.Proof.ArcGeometry.Main
import LiuWang.Proof.ChebyshevBound.IntegratedFormula.Sharp

/-!
# 原闭窗口的单位圆周能量

复用整数频率的有限 Parseval；自然数频率经单射嵌入，不改变闭下端点。
`charReal` 已含 `2π`，任意长度一窗口均没有额外归一化因子。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Interval

namespace LiuWang.Proof.MinorArcEnergy

open Interfaces Parameters ArcGeometry AnalyticNumberTheory.LargeSieve

theorem continuous_S (N : ℕ) : Continuous (S N) := by
  unfold S Fourier.liuWangExpSum Fourier.indexedExpSum charReal
  fun_prop

theorem continuous_energy (N : ℕ) : Continuous (fun α : ℝ => ‖S N α‖ ^ 2) :=
  (continuous_S N).norm.pow 2

theorem energy_integrableOn (N : ℕ) (a b : ℝ) :
    IntegrableOn (fun α : ℝ => ‖S N α‖ ^ 2) (Set.Icc a b) :=
  (continuous_energy N).integrableOn_Icc

theorem integral_S_sq (N : ℕ) (u : ℝ) :
    (∫ α in u..u + 1, ‖S N α‖ ^ 2) =
      ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  let e : ℕ ↪ ℤ := ⟨fun n => (n : ℤ), Nat.cast_injective⟩
  have h := chen1973_fourier_parseval ((windowFinset N).map e)
    (fun k => (ArithmeticFunction.vonMangoldt k.toNat : ℂ)) u
  simpa [Finset.sum_map, e, S, Fourier.liuWangExpSum, Fourier.indexedExpSum,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem setIntegral_S_sq (N : ℕ) (u : ℝ) :
    (∫ α in Set.Icc u (u + 1), ‖S N α‖ ^ 2) =
      ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show u ≤ u + 1 by linarith)]
  exact integral_S_sq N u

theorem source_energy_eq (N : ℕ) :
    (∫ α in sourceDomain N, ‖S N α‖ ^ 2) =
      ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  simpa only [sourceDomain, add_comm] using setIntegral_S_sq N (1 / sourceQ N)

theorem window_subset_Icc {N : ℕ} (hN : 0 < N) :
    windowFinset N ⊆ Finset.Icc 1 N := by
  intro n hn
  have hn' := (mem_windowFinset_iff N n).1 hn
  exact Finset.mem_Icc.2 ⟨by
    have := hn'.2
    by_contra h
    have : n = 0 := by omega
    simp_all, hn'.1⟩

theorem window_sq_le_prefix {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg (window_subset_Icc hN)
    (fun _ _ _ => sq_nonneg _)

theorem source_energy_le_mother {N : ℕ} (hN : 0 < N) :
    (∫ α in sourceDomain N, ‖S N α‖ ^ 2) ≤
      Real.log N * Chebyshev.psi (N : ℝ) := by
  rw [source_energy_eq]
  exact ChebyshevBound.sum_mangoldt_sq_subset_le_log_mul_psi
    (windowFinset N) (window_subset_Icc hN)

theorem source_energy_le_sharp {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ α in sourceDomain N, ‖S N α‖ ^ 2) ≤
      1.0012 * (N : ℝ) * Real.log N := by
  have hpos : 0 < N := by
    exact_mod_cast (Real.exp_pos 3100).trans_le hN
  rw [source_energy_eq]
  exact (window_sq_le_prefix hpos).trans
    (ChebyshevBound.IntegratedFormula.sum_mangoldt_sq_le_sharp hN)

theorem set_energy_nonneg (N : ℕ) (s : Set ℝ) :
    0 ≤ ∫ α in s, ‖S N α‖ ^ 2 :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem set_energy_le_source (N : ℕ) {s : Set ℝ} (hs : s ⊆ sourceDomain N) :
    (∫ α in s, ‖S N α‖ ^ 2) ≤ ∫ α in sourceDomain N, ‖S N α‖ ^ 2 :=
  setIntegral_mono_set (energy_integrableOn N _ _)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hs.eventuallyLE

end LiuWang.Proof.MinorArcEnergy
