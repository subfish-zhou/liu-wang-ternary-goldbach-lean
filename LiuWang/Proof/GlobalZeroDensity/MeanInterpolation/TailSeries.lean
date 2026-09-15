import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.TailFiniteMean

/-! The actual Mobius tail, with finite truncations and an absolutely convergent limit. -/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory Filter
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

def muCoefficient (σ : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (fun k => (ArithmeticFunction.moebius k : ℂ)) σ n

def tailPartial (N k : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ range k, LSeries.term (fun j => (ArithmeticFunction.moebius j : ℂ))
    ((σ : ℂ) + t * I) (n + N)

theorem mu_term_wave (σ t : ℝ) (n : ℕ) :
    LSeries.term (fun j => (ArithmeticFunction.moebius j : ℂ)) ((σ : ℂ) + t * I) n =
      muCoefficient σ n * wave (-Real.log n) t := by
  by_cases hn : n = 0
  · subst n; simp [muCoefficient]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, muCoefficient, LSeries.term_of_ne_zero hn,
    Complex.cpow_add _ _ hn0]
  have he : ((n : ℂ) ^ ((t : ℂ) * I))⁻¹ = wave (-Real.log n) t := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_neg]
    unfold wave
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  simp only [div_eq_mul_inv, mul_inv_rev, he]
  ring

theorem tailPartial_eq_polynomial (N k : ℕ) (σ t : ℝ) :
    tailPartial N k σ t =
      exponentialPolynomial ((range k).image (fun n => n + N))
        (muCoefficient σ) (fun n => -Real.log n) t := by
  unfold tailPartial exponentialPolynomial
  rw [sum_image (fun a _ b _ h => Nat.add_right_cancel h)]
  exact sum_congr rfl (fun n _ => mu_term_wave σ t (n + N))

theorem norm_muCoefficient {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    ‖muCoefficient σ n‖ ≤ (n : ℝ) ^ (-σ) := by
  simpa [muCoefficient] using norm_mu_term_le (s := (σ : ℂ)) (by simpa using hσ) n

theorem tailPartial_continuous (N k : ℕ) (σ : ℝ) :
    Continuous (tailPartial N k σ) := by
  simp_rw [funext (tailPartial_eq_polynomial N k σ)]
  unfold exponentialPolynomial wave
  fun_prop

theorem tailPartial_bound {σ : ℝ} (hσ : 1 < σ) (N k : ℕ) (t : ℝ) :
    ‖tailPartial N k σ t‖ ≤ 1 + 1 / (σ - 1) := by
  rw [tailPartial_eq_polynomial]
  unfold exponentialPolynomial
  calc
    _ ≤ ∑ n ∈ (range k).image (fun n => n + N), ‖muCoefficient σ n * wave (-Real.log n) t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (range k).image (fun n => n + N), (n : ℝ) ^ (-σ) := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, norm_wave, mul_one]
      exact norm_muCoefficient hσ n
    _ ≤ _ := finite_power_sum _ hσ

theorem tailPartial_tendsto {σ : ℝ} (hσ : 1 < σ) (N : ℕ) (t : ℝ) :
    Tendsto (fun k : ℕ => tailPartial N k σ t) atTop
      (𝓝 (∑' n : ℕ, LSeries.term (fun j => (ArithmeticFunction.moebius j : ℂ))
        ((σ : ℂ) + t * I) (n + N))) := by
  have hs := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr
    (show 1 < ((σ : ℂ) + t * I).re by simpa using hσ)
  have htail := (summable_nat_add_iff N).mpr hs
  exact htail.hasSum.tendsto_sum_nat

theorem tailPartial_mean {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 2 ≤ N)
    (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖tailPartial N k σ t‖ ^ 2) ≤
      2 * T / ((N : ℝ) - 1) +
      8 * (3 * (1 + 1 / (2 * σ - 2)) +
        (1 / (σ - 1)) * (1 + 1 / (σ - 1))) +
      8 * (1 + 1 / (σ - 1)) ^ 2 := by
  simp_rw [tailPartial_eq_polynomial]
  apply finite_tail_mean hN
    (fun n hn => by obtain ⟨j, _, rfl⟩ := mem_image.mp hn; omega) hσ
    (fun n _ => norm_muCoefficient hσ n) hT

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
