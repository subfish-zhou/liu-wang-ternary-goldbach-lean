import LiuWang.Proof.Interfaces.Main
import LiuWang.Proof.SingularIntegral.Geometry
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# 真实复幂窗与 Fourier 符号

`windowWeight` 仅把原区间权延零到实线；闭端点与区间积分的差由
Lebesgue 单点零测定理处理。这里不展开三重频率积分。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set FourierTransform
open scoped Interval
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SingularIntegral

def windowWeight (N : ℕ) (rho : ℂ) : ℝ → ℂ :=
  (Icc (sourceWindowLower N) (N : ℝ)).indicator (fun t => (t : ℂ) ^ (rho - 1))

theorem window_lower_pos {N : ℕ} (hN : 0 < N) : 0 < sourceWindowLower N := by
  dsimp [sourceWindowLower]
  positivity

theorem window_lower_le (N : ℕ) : sourceWindowLower N ≤ (N : ℝ) := by
  dsimp [sourceWindowLower]
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem cpow_continuousOn_window {N : ℕ} (hN : 0 < N) (z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ z) (Icc (sourceWindowLower N) N) := by
  intro t ht
  exact (Complex.continuousAt_ofReal_cpow_const t z
    (Or.inr (ne_of_gt ((window_lower_pos hN).trans_le ht.1)))).continuousWithinAt

theorem cpow_intervalIntegrable {N : ℕ} (hN : 0 < N) (z : ℂ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ z) volume (sourceWindowLower N) N :=
  (cpow_continuousOn_window hN z).intervalIntegrable_of_Icc (window_lower_le N)

theorem windowWeight_integrable {N : ℕ} (hN : 0 < N) (rho : ℂ) :
    Integrable (windowWeight N rho) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact (cpow_continuousOn_window hN (rho - 1)).integrableOn_compact isCompact_Icc

theorem windowWeight_stronglyMeasurable (N : ℕ) (rho : ℂ) :
    StronglyMeasurable (windowWeight N rho) := by
  exact (Complex.measurable_ofReal.pow_const _).stronglyMeasurable.indicator measurableSet_Icc

theorem charReal_eq_fourierChar (u : ℝ) :
    charReal u = (Real.fourierChar u : ℂ) := by
  simp [charReal, Real.fourierChar_apply, mul_assoc]

theorem charReal_norm (u : ℝ) : ‖charReal u‖ = 1 := by
  rw [charReal_eq_fourierChar]
  exact Circle.norm_coe _

theorem charReal_continuous : Continuous charReal := by
  unfold charReal
  fun_prop

theorem Jrho_intervalIntegrable {N : ℕ} (hN : 0 < N) (rho : ℂ) (eta : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (rho - 1) * charReal (eta * t))
      volume (sourceWindowLower N) N :=
  ((cpow_continuousOn_window hN (rho - 1)).mul
    (charReal_continuous.comp (continuous_const.mul continuous_id)).continuousOn
    ).intervalIntegrable_of_Icc (window_lower_le N)

theorem Jrho_eq_fourier_neg (N : ℕ) (rho : ℂ) (eta : ℝ) :
    Jrho N rho eta = 𝓕 (windowWeight N rho) (-eta) := by
  rw [Real.fourier_real_eq]
  simp only [Circle.smul_def, smul_eq_mul, ← charReal_eq_fourierChar, mul_neg, neg_neg]
  rw [show (fun t : ℝ => charReal (t * eta) * windowWeight N rho t) =
      (Icc (sourceWindowLower N) (N : ℝ)).indicator
        (fun t => (t : ℂ) ^ (rho - 1) * charReal (eta * t)) by
    ext t
    by_cases ht : t ∈ Icc (sourceWindowLower N) (N : ℝ)
    · simp [windowWeight, ht, mul_comm]
    · simp [windowWeight, ht] ]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (window_lower_le N)]
  rfl

theorem Jrho_eq_fourierInv (N : ℕ) (rho : ℂ) (eta : ℝ) :
    Jrho N rho eta = 𝓕⁻ (windowWeight N rho) eta := by
  rw [Real.fourierInv_eq_fourier_neg, Jrho_eq_fourier_neg]

theorem Jrho_one_eq_J (N : ℕ) (eta : ℝ) : Jrho N 1 eta = J N eta := by
  simp [Jrho, J]

theorem simplex_cpow_continuousOn (N : ℝ) (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    ContinuousOn (fun x : ℝ × ℝ =>
      ((N * x.1 : ℝ) : ℂ) ^ (rho₁ - 1) *
      ((N * x.2 : ℝ) : ℂ) ^ (rho₂ - 1) *
      ((N * (1 - x.1 - x.2) : ℝ) : ℂ) ^ (rho₃ - 1)) triangle := by
  intro x hx
  have hx' : x ∈ sourceSimplex := sourceSimplex_eq_triangle ▸ hx
  have hp₁ : 0 < N * x.1 := mul_pos hN (lt_of_lt_of_le (by norm_num) hx'.1)
  have hp₂ : 0 < N * x.2 := mul_pos hN (lt_of_lt_of_le (by norm_num) hx'.2.2.1)
  have hp₃ : 0 < N * (1 - x.1 - x.2) :=
    mul_pos hN (lt_of_lt_of_le (by norm_num) hx'.2.2.2.2.1)
  have h₁ : ContinuousAt (fun y : ℝ × ℝ => ((N * y.1 : ℝ) : ℂ) ^ (rho₁ - 1)) x :=
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp₁.ne')).comp
      (f := fun y : ℝ × ℝ => N * y.1)
      (continuous_const.mul continuous_fst).continuousAt
  have h₂ : ContinuousAt (fun y : ℝ × ℝ => ((N * y.2 : ℝ) : ℂ) ^ (rho₂ - 1)) x :=
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp₂.ne')).comp
      (f := fun y : ℝ × ℝ => N * y.2)
      (continuous_const.mul continuous_snd).continuousAt
  have h₃ : ContinuousAt (fun y : ℝ × ℝ =>
      ((N * (1 - y.1 - y.2) : ℝ) : ℂ) ^ (rho₃ - 1)) x :=
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp₃.ne')).comp
      (f := fun y : ℝ × ℝ => N * (1 - y.1 - y.2))
      (continuous_const.mul ((continuous_const.sub continuous_fst).sub continuous_snd)).continuousAt
  exact ((h₁.mul h₂).mul h₃).continuousWithinAt

theorem simplex_cpow_integrableOn (N : ℝ) (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    IntegrableOn (fun x : ℝ × ℝ =>
      ((N * x.1 : ℝ) : ℂ) ^ (rho₁ - 1) *
      ((N * x.2 : ℝ) : ℂ) ^ (rho₂ - 1) *
      ((N * (1 - x.1 - x.2) : ℝ) : ℂ) ^ (rho₃ - 1)) triangle :=
  (simplex_cpow_continuousOn N hN rho₁ rho₂ rho₃).integrableOn_compact triangle_isCompact

end LiuWang.Proof.SingularIntegral
