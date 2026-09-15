import LiuWang.Proof.NonprincipalDensityAdvance.CharacterEnergy
import LiuWang.Proof.GlobalZeroDensity.Sharp.FiniteMean

/-!
# Fixed-level vertical energy, with exact principal subtraction

The residue fibers are kept before integration. No primitive-character sieve
or bound for an L-function mean is assumed.
-/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans

def fiber (q : ℕ) (S : Finset ℕ) (x : ZMod q) : Finset ℕ :=
  S.filter (fun n : ℕ => (n : ZMod q) = x)

def polynomial {q : ℕ} (chi : Character q) (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  characterPolynomial chi S (fun n => a n * wave (w n) t)

def familyMean (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y, ‖polynomial chi S a w t‖ ^ 2) / q.totient

def principalMean (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (y : ℝ) : ℝ :=
  (∫ t in -y..y, ‖polynomial (1 : Character q) S a w t‖ ^ 2) / q.totient

theorem continuous_polynomial {q : ℕ} (chi : Character q) (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) : Continuous (polynomial chi S a w) := by
  unfold polynomial characterPolynomial wave
  fun_prop

theorem polynomial_integrable {q : ℕ} (chi : Character q) (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (y : ℝ) :
    IntervalIntegrable (fun t => ‖polynomial chi S a w t‖ ^ 2) volume (-y) y :=
  ((continuous_polynomial chi S a w).norm.pow 2).intervalIntegrable _ _

theorem fiber_integrable (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (y : ℝ) :
    IntervalIntegrable (fun t => ‖exponentialPolynomial S a w t‖ ^ 2) volume (-y) y := by
  apply Continuous.intervalIntegrable
  unfold exponentialPolynomial wave
  fun_prop

theorem familyMean_eq_integral (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (y : ℝ) :
    familyMean q S a w y =
      ∫ t in -y..y, (∑ chi ∈ nonprincipalCharacters q, ‖polynomial chi S a w t‖ ^ 2) /
        q.totient := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
  · rfl
  · exact fun chi _ => polynomial_integrable chi S a w y

theorem familyMean_exact (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (y : ℝ) :
    familyMean q S a w y =
      (∑ x : ZMod q, if IsUnit x then
        ∫ t in -y..y, ‖exponentialPolynomial (fiber q S x) a w t‖ ^ 2 else 0) -
      principalMean q S a w y := by
  have he (t : ℝ) :
      (∑ chi ∈ nonprincipalCharacters q, ‖polynomial chi S a w t‖ ^ 2) / q.totient =
        (∑ x : ZMod q, if IsUnit x then
          ‖exponentialPolynomial (fiber q S x) a w t‖ ^ 2 else 0) -
        ‖polynomial (1 : Character q) S a w t‖ ^ 2 / q.totient := by
    exact normalized_nonprincipal_energy q S (fun n => a n * wave (w n) t)
  have hx (x : ZMod q) :
      IntervalIntegrable (fun t => if IsUnit x then
        ‖exponentialPolynomial (fiber q S x) a w t‖ ^ 2 else 0) volume (-y) y := by
    split_ifs
    · exact fiber_integrable _ _ _ _
    · exact intervalIntegrable_const
  rw [familyMean_eq_integral]
  simp_rw [he]
  have hsum : IntervalIntegrable (fun t => ∑ x : ZMod q, if IsUnit x then
      ‖exponentialPolynomial (fiber q S x) a w t‖ ^ 2 else 0) volume (-y) y := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum univ (fun x _ => hx x)
  rw [intervalIntegral.integral_sub hsum
    ((polynomial_integrable (1 : Character q) S a w y).div_const (q.totient : ℝ)),
    intervalIntegral.integral_finsetSum (fun x _ => hx x), intervalIntegral.integral_div]
  congr 1
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem familyMean_nonneg (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ familyMean q S a w y := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun chi _ =>
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

theorem principalMean_nonneg (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ principalMean q S a w y :=
  div_nonneg (intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem familyMean_oscillatory_identity (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (y : ℝ) :
    ((familyMean q S a w y + principalMean q S a w y : ℝ) : ℂ) =
      ∑ x : ZMod q, if IsUnit x then
        ∑ m ∈ fiber q S x, ∑ n ∈ fiber q S x,
          a m * conj (a n) * ∫ t in -y..y, wave (w m - w n) t else 0 := by
  rw [familyMean_exact, sub_add_cancel, Complex.ofReal_sum]
  apply sum_congr rfl
  intro x _
  split_ifs
  · exact polynomial_integral_expansion _ _ _ _
  · simp

theorem familyMean_diagonal_offDiagonal (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (hw : Set.InjOn w S) {y : ℝ} (hy : 0 ≤ y) :
    familyMean q S a w y ≤
      (∑ x : ZMod q, if IsUnit x then
        2 * y * ∑ n ∈ fiber q S x, ‖a n‖ ^ 2 +
        2 * ∑ m ∈ fiber q S x, ∑ n ∈ (fiber q S x).erase m,
          ‖a m‖ * ‖a n‖ / |w m - w n| else 0) -
      principalMean q S a w y := by
  rw [familyMean_exact]
  apply sub_le_sub_right
  apply sum_le_sum
  intro x _
  split_ifs
  · exact finite_mean_le _ a w (hw.mono (filter_subset _ _)) hy
  · rfl

end LiuWang.Proof.NonprincipalDensityMeans
