import LiuWang.Proof.NonprincipalDensityMeans.MeanBound
import LiuWang.Proof.GlobalZeroDensity.Sharp.MeanBound

/-! # Actual Mobius-mollifier vertical means at the original modulus -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans

def Qmean (q : ℕ) [NeZero q] (X sigma y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
    ‖NonprincipalDensityAdvance.Q chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

theorem Q_eq_dirichletPolynomial {q : ℕ} (chi : Character q) (X : ℝ) (s : ℂ) :
    NonprincipalDensityAdvance.Q chi X s =
      dirichletPolynomial chi ((range ⌈X⌉₊).erase 0)
        (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  unfold NonprincipalDensityAdvance.Q dirichletPolynomial twistedMu
  have he : (∑ n ∈ (range ⌈X⌉₊).erase 0,
      chi n * (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s) =
      ∑ n ∈ range ⌈X⌉₊, chi n * (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s := by
    apply sum_subset (erase_subset _ _)
    intro n hn hn'
    have : n = 0 := by simpa only [mem_erase, hn, and_true, not_not] using hn'
    simp [this]
  rw [← he]
  apply sum_congr rfl
  intro n _
  rw [mul_comm]

theorem Q_vertical_integrable {q : ℕ} (chi : Character q) (X sigma y : ℝ) :
    IntervalIntegrable (fun t =>
      ‖NonprincipalDensityAdvance.Q chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y := by
  simp_rw [Q_eq_dirichletPolynomial]
  exact dirichletPolynomial_integrable chi _ (fun _ hn =>
    Nat.pos_of_ne_zero (mem_erase.mp hn).1) _ _ _

theorem vertical_criticalCoefficient_eq :
    verticalCoefficient (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2) =
      criticalCoefficient := by
  funext n
  simp only [verticalCoefficient, criticalCoefficient, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

theorem Q_critical_eq_wave {q : ℕ} (chi : Character q) (X t : ℝ) :
    NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I) =
      polynomial chi ((range ⌈X⌉₊).erase 0) criticalCoefficient (fun n => -Real.log n) t := by
  rw [Q_eq_dirichletPolynomial]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    vertical_criticalCoefficient_eq] using
    dirichletPolynomial_eq_wave chi ((range ⌈X⌉₊).erase 0)
      (fun _ hn => Nat.pos_of_ne_zero (mem_erase.mp hn).1)
      (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2) t

theorem Qmean_critical_eq (q : ℕ) [NeZero q] (X y : ℝ) :
    Qmean q X (1 / 2) y =
      familyMean q ((range ⌈X⌉₊).erase 0) criticalCoefficient (fun n => -Real.log n) y := by
  unfold Qmean
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp_rw [Q_critical_eq_wave]
  rfl

theorem Qmean_critical_residue_identity (q : ℕ) [NeZero q] (X y : ℝ) :
    Qmean q X (1 / 2) y =
      (∑ x : ZMod q, if IsUnit x then
        ∫ t in -y..y, ‖exponentialPolynomial
          (fiber q ((range ⌈X⌉₊).erase 0) x) criticalCoefficient
          (fun n => -Real.log n) t‖ ^ 2 else 0) -
      (∫ t in -y..y,
        ‖NonprincipalDensityAdvance.Q (1 : Character q) X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) /
        q.totient := by
  rw [Qmean_critical_eq, familyMean_exact]
  simp_rw [Q_critical_eq_wave]
  rfl

def mollifierMeanBound (q : ℕ) (X y : ℝ) : ℝ :=
  meanFactor q ⌈X⌉₊ y * harmonicRange ⌈X⌉₊

theorem mollifierMeanBound_nonneg (q : ℕ) (X : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ mollifierMeanBound q X y :=
  mul_nonneg (meanFactor_nonneg q _ hy) (harmonicRange_nonneg _)

theorem criticalCoefficient_energy_le (N : ℕ) :
    (∑ n ∈ (range N).erase 0, ‖criticalCoefficient n‖ ^ 2) ≤ harmonicRange N := by
  have he : (∑ n ∈ (range N).erase 0, ‖criticalCoefficient n‖ ^ 2) =
      ∑ n ∈ (range N).erase 0, (ArithmeticFunction.moebius n : ℝ) ^ 2 / n := by
    apply sum_congr rfl
    intro n hn
    exact criticalCoefficient_sq (Nat.pos_of_ne_zero (mem_erase.mp hn).1)
  rw [he]
  exact mollifier_energy_le_inverse_range N

theorem Qmean_critical_le_with_principal (q : ℕ) [NeZero q] (X : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Qmean q X (1 / 2) y ≤ mollifierMeanBound q X y -
      (∫ t in -y..y,
        ‖NonprincipalDensityAdvance.Q (1 : Character q) X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) /
        q.totient := by
  rw [Qmean_critical_eq]
  have h := familyMean_le q (Subset.refl ((range ⌈X⌉₊).erase 0)) criticalCoefficient hy
  have hE := (unitEnergy_le q ((range ⌈X⌉₊).erase 0) criticalCoefficient).trans
    (criticalCoefficient_energy_le ⌈X⌉₊)
  have hb := mul_le_mul_of_nonneg_left hE (meanFactor_nonneg q ⌈X⌉₊ hy)
  apply h.trans
  simp_rw [Q_critical_eq_wave]
  exact sub_le_sub_right hb _

theorem Qmean_critical_le (q : ℕ) [NeZero q] (X : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Qmean q X (1 / 2) y ≤ mollifierMeanBound q X y := by
  apply (Qmean_critical_le_with_principal q X hy).trans
  apply sub_le_self
  exact div_nonneg (intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem Qmean_critical_log_bound (q : ℕ) [NeZero q] (X : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Qmean q X (1 / 2) y ≤
      (2 * y + 4 * (⌈X⌉₊ : ℝ) / q * (1 + Real.log (⌈X⌉₊ / q + 1 : ℕ))) *
        (1 + Real.log ⌈X⌉₊) := by
  have hN := inverse_range_le_log ⌈X⌉₊
  have hK := inverse_range_le_log (⌈X⌉₊ / q + 1)
  have he : meanFactor q ⌈X⌉₊ y =
      2 * y + 4 * (⌈X⌉₊ : ℝ) / q * harmonicRange (⌈X⌉₊ / q + 1) := by
    unfold meanFactor logRowBound
    ring
  have hfac : meanFactor q ⌈X⌉₊ y ≤
      2 * y + 4 * (⌈X⌉₊ : ℝ) / q * (1 + Real.log (⌈X⌉₊ / q + 1 : ℕ)) := by
    rw [he]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hK
      (by positivity : 0 ≤ 4 * (⌈X⌉₊ : ℝ) / q))
  apply (Qmean_critical_le q X hy).trans
  exact mul_le_mul hfac hN (harmonicRange_nonneg _) ((meanFactor_nonneg q _ hy).trans hfac)

@[simp] theorem Qmean_one (X sigma y : ℝ) : Qmean 1 X sigma y = 0 := by
  simp [Qmean]

@[simp] theorem Qmean_two (X sigma y : ℝ) : Qmean 2 X sigma y = 0 := by
  simp [Qmean]

end LiuWang.Proof.NonprincipalDensityMeans
