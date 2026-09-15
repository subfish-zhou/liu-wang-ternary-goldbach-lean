import LiuWang.Proof.NonprincipalPsi.Consumer
import LiuWang.Proof.OscillatoryBounds.Weighted
import Mathlib.NumberTheory.AbelSummation

/-!
# 真实自然前缀到闭窗的 Abel 恒等式

冻结 Abel 生产者给出左开区间；`lowerTerm` 保留闭下端点的单项。
运输算子不包含任何 psi 近似假设。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.OscillatoryBounds

namespace LiuWang.Proof.NonprincipalExpansion

def phaseDerivative (η t : ℝ) : ℂ :=
  charReal (η * t) * (2 * Real.pi * η * Complex.I)

def abelTransform (N : ℕ) (η : ℝ) (F : ℝ → ℂ) : ℂ :=
  charReal (η * N) * F N -
    charReal (η * sourceWindowLower N) * F (sourceWindowLower N) -
    ∫ t in sourceWindowLower N..(N : ℝ), phaseDerivative η t * F t

def lowerTerm (N : ℕ) (c : ℕ → ℂ) (η : ℝ) : ℂ :=
  if (⌊sourceWindowLower N⌋₊ : ℝ) = sourceWindowLower N then
    c ⌊sourceWindowLower N⌋₊ * charReal (η * sourceWindowLower N)
  else 0

def S_chi {q : ℕ} (N : ℕ) (chi : Character q) (η : ℝ) : ℂ :=
  ∑ n ∈ windowFinset N,
    (ArithmeticFunction.vonMangoldt n : ℂ) * chi n * charReal (η * n)

theorem lower_nonneg (N : ℕ) : 0 ≤ sourceWindowLower N := by
  unfold sourceWindowLower
  positivity

theorem lower_le (N : ℕ) : sourceWindowLower N ≤ (N : ℝ) := by
  unfold sourceWindowLower
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem mem_window_real (N n : ℕ) :
    n ∈ windowFinset N ↔ sourceWindowLower N ≤ (n : ℝ) ∧ n ≤ N := by
  rw [mem_windowFinset_iff, mem_windowSet_iff]
  have h : sourceWindowLower N ≤ (n : ℝ) ↔ N ≤ 1000 * n := by
    unfold sourceWindowLower
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)]
    norm_cast
    omega
  rw [h, and_comm]

theorem sum_window_eq_Ioc_add_lower (N : ℕ) (c : ℕ → ℂ) (η : ℝ) :
    (∑ n ∈ windowFinset N, c n * charReal (η * n)) =
      (∑ n ∈ Finset.Ioc ⌊sourceWindowLower N⌋₊ N, c n * charReal (η * n)) +
        lowerTerm N c η := by
  classical
  have hf : ⌊sourceWindowLower N⌋₊ ≤ N := by
    simpa using Nat.floor_le_floor (lower_le N)
  have hmem (n : ℕ) :
      n ∈ Finset.Ioc ⌊sourceWindowLower N⌋₊ N ↔
        sourceWindowLower N < (n : ℝ) ∧ n ≤ N := by
    rw [Finset.mem_Ioc, Nat.floor_lt (lower_nonneg N)]
  by_cases he : (⌊sourceWindowLower N⌋₊ : ℝ) = sourceWindowLower N
  · have hw : windowFinset N =
        insert ⌊sourceWindowLower N⌋₊ (Finset.Ioc ⌊sourceWindowLower N⌋₊ N) := by
      ext n
      rw [mem_window_real, Finset.mem_insert, hmem, ← he]
      simp only [Nat.floor_natCast]
      constructor
      · rintro ⟨hn, hnN⟩
        have hn' : ⌊sourceWindowLower N⌋₊ ≤ n := by exact_mod_cast hn
        rcases eq_or_lt_of_le hn' with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨by exact_mod_cast h, hnN⟩
      · rintro (rfl | ⟨hn, hnN⟩)
        · exact ⟨le_rfl, hf⟩
        · exact ⟨hn.le, hnN⟩
    rw [hw, Finset.sum_insert (by simp), lowerTerm, if_pos he]
    simp only [he]
    ring
  · have hw : windowFinset N = Finset.Ioc ⌊sourceWindowLower N⌋₊ N := by
      ext n
      rw [mem_window_real, hmem]
      constructor
      · rintro ⟨hn, hnN⟩
        refine ⟨lt_of_le_of_ne hn ?_, hnN⟩
        intro h
        apply he
        rw [h, Nat.floor_natCast]
      · exact fun h => ⟨h.1.le, h.2⟩
    simp [hw, lowerTerm, he]

theorem sum_prefix_zero (c : ℕ → ℂ) (hc : c 0 = 0) (m : ℕ) :
    ∑ n ∈ Finset.Icc 0 m, c n = ∑ n ∈ Finset.Icc 1 m, c n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn hn'
    have : n = 0 := by
      simp only [Finset.mem_Icc] at hn hn'
      omega
    simpa [this] using hc

theorem phaseDerivative_continuous (η : ℝ) : Continuous (phaseDerivative η) :=
  (continuous_charReal_mul η).mul continuous_const

theorem prefix_phase_integrable (N : ℕ) (c : ℕ → ℂ) (η : ℝ) :
    IntervalIntegrable
      (fun t => phaseDerivative η t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)
      volume (sourceWindowLower N) N := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (lower_le N)]
  exact integrableOn_mul_sum_Icc c (lower_nonneg N)
    (phaseDerivative_continuous η).continuousOn.integrableOn_Icc

theorem closed_window_abel (N : ℕ) (c : ℕ → ℂ) (hc : c 0 = 0) (η : ℝ) :
    (∑ n ∈ windowFinset N, c n * charReal (η * n)) =
      abelTransform N η (fun t => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n) +
        lowerTerm N c η := by
  have hd : deriv (fun t => charReal (η * t)) = phaseDerivative η := by
    funext t
    exact (hasDerivAt_charReal_mul η t).deriv
  have h := sum_mul_eq_sub_sub_integral_mul c (lower_nonneg N) (lower_le N)
    (fun t _ => (hasDerivAt_charReal_mul η t).differentiableAt)
    (by rw [hd]; exact (phaseDerivative_continuous η).continuousOn.integrableOn_Icc)
  rw [← intervalIntegral.integral_of_le (lower_le N), hd] at h
  simp only [sum_prefix_zero c hc, Nat.floor_natCast] at h
  rw [sum_window_eq_Ioc_add_lower]
  unfold abelTransform
  simp only [Nat.floor_natCast]
  congr 1
  simpa only [mul_comm] using h

theorem S_chi_abel {q : ℕ} (N : ℕ) (chi : Character q) (η : ℝ) :
    S_chi N chi η = abelTransform N η (ExplicitPerron.psi chi) +
      lowerTerm N (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) η := by
  exact closed_window_abel N _ (by simp) η

theorem psi_phase_integrable {q : ℕ} (N : ℕ) (chi : Character q) (η : ℝ) :
    IntervalIntegrable (fun t => phaseDerivative η t * ExplicitPerron.psi chi t)
      volume (sourceWindowLower N) N := by
  simpa only [ExplicitPerron.psi_eq_sum,
    sum_prefix_zero (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * chi n)
      (by simp)] using
    prefix_phase_integrable N (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) η

theorem abelTransform_add (N : ℕ) (η : ℝ) (F G : ℝ → ℂ)
    (hF : IntervalIntegrable (fun t => phaseDerivative η t * F t)
      volume (sourceWindowLower N) N)
    (hG : IntervalIntegrable (fun t => phaseDerivative η t * G t)
      volume (sourceWindowLower N) N) :
    abelTransform N η (fun t => F t + G t) =
      abelTransform N η F + abelTransform N η G := by
  simp only [abelTransform, mul_add, intervalIntegral.integral_add hF hG]
  ring

end LiuWang.Proof.NonprincipalExpansion
