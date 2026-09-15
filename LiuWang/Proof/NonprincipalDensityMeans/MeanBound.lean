import LiuWang.Proof.NonprincipalDensityMeans.LogGaps

/-! # Explicit fixed-modulus finite Dirichlet-polynomial mean inequality -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans

def unitEnergy (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, if IsUnit (n : ZMod q) then ‖a n‖ ^ 2 else 0

def meanFactor (q N : ℕ) (y : ℝ) : ℝ := 2 * y + 2 * logRowBound q N

theorem meanFactor_nonneg (q N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ meanFactor q N y := by
  unfold meanFactor
  linarith [logRowBound_nonneg q N]

theorem unitEnergy_nonneg (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ unitEnergy q S a := by
  apply sum_nonneg
  intro n _
  split_ifs <;> positivity

theorem unitEnergy_le (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) :
    unitEnergy q S a ≤ ∑ n ∈ S, ‖a n‖ ^ 2 := by
  apply sum_le_sum
  intro n _
  split_ifs
  · rfl
  · exact sq_nonneg _

theorem fiber_unit_sum (q : ℕ) [NeZero q] (S : Finset ℕ) (g : ℕ → ℝ) :
    (∑ x : ZMod q, if IsUnit x then ∑ n ∈ fiber q S x, g n else 0) =
      ∑ n ∈ S, if IsUnit (n : ZMod q) then g n else 0 := by
  rw [← sum_fiberwise (s := S) (g := fun n : ℕ => (n : ZMod q))
    (f := fun n => if IsUnit (n : ZMod q) then g n else 0)]
  apply sum_congr rfl
  intro x _
  have he : (∑ n ∈ fiber q S x, if IsUnit (n : ZMod q) then g n else 0) =
      ∑ n ∈ fiber q S x, if IsUnit x then g n else 0 := by
    apply sum_congr rfl
    intro n hn
    rw [(mem_filter.mp hn).2]
  change _ = ∑ n ∈ fiber q S x, _
  rw [he]
  split_ifs <;> simp

theorem familyMean_le (q : ℕ) [NeZero q] {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) (a : ℕ → ℂ) {y : ℝ} (hy : 0 ≤ y) :
    familyMean q S a (fun n => -Real.log n) y ≤
      meanFactor q N y * unitEnergy q S a -
        principalMean q S a (fun n => -Real.log n) y := by
  have h := familyMean_diagonal_offDiagonal q S a (fun n => -Real.log n)
    ((negative_log_inj N).mono hS) hy
  have he (m n : ℕ) : |-Real.log m - -Real.log n| = |Real.log m - Real.log n| := by
    rw [show -Real.log m - -Real.log n = -(Real.log m - Real.log n) by ring, abs_neg]
  simp_rw [he] at h
  apply h.trans
  apply sub_le_sub_right
  calc
    _ ≤ ∑ x : ZMod q, if IsUnit x then
        meanFactor q N y * ∑ n ∈ fiber q S x, ‖a n‖ ^ 2 else 0 := by
      apply sum_le_sum
      intro x _
      split_ifs
      · have ho := fiber_offDiagonal_le hS x a
        unfold meanFactor
        nlinarith only [ho]
      · rfl
    _ = _ := by
      have hfu : (∑ x : ZMod q, if IsUnit x then
          ∑ n ∈ fiber q S x, ‖a n‖ ^ 2 else 0) = unitEnergy q S a :=
        fiber_unit_sum q S (fun n => ‖a n‖ ^ 2)
      rw [← hfu, mul_sum]
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp

theorem familyMean_le_without_principal (q : ℕ) [NeZero q] {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) (a : ℕ → ℂ) {y : ℝ} (hy : 0 ≤ y) :
    familyMean q S a (fun n => -Real.log n) y ≤ meanFactor q N y * unitEnergy q S a :=
  (familyMean_le q hS a hy).trans (sub_le_self _ (principalMean_nonneg q S a _ hy))

def verticalCoefficient (c : ℕ → ℂ) (sigma : ℝ) (n : ℕ) : ℂ :=
  c n / (n : ℂ) ^ (sigma : ℂ)

def dirichletPolynomial {q : ℕ} (chi : Character q) (S : Finset ℕ)
    (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, c n * chi n / (n : ℂ) ^ s

theorem term_vertical_wave (c : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (sigma t : ℝ) :
    c n / (n : ℂ) ^ ((sigma : ℂ) + t * Complex.I) =
      verticalCoefficient c sigma n * wave (-Real.log n) t := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [Complex.cpow_add _ _ hn0]
  have he : ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ = wave (-Real.log n) t := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_neg]
    unfold wave
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  simp only [verticalCoefficient, div_eq_mul_inv, mul_inv_rev, he]
  ring

theorem dirichletPolynomial_eq_wave {q : ℕ} (chi : Character q) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (c : ℕ → ℂ) (sigma t : ℝ) :
    dirichletPolynomial chi S c ((sigma : ℂ) + t * Complex.I) =
      polynomial chi S (verticalCoefficient c sigma) (fun n => -Real.log n) t := by
  apply sum_congr rfl
  intro n hn
  have h := term_vertical_wave c (hS n hn) sigma t
  change c n * chi n / _ = _
  rw [mul_div_right_comm, h]

theorem dirichletPolynomial_integrable {q : ℕ} (chi : Character q) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (c : ℕ → ℂ) (sigma y : ℝ) :
    IntervalIntegrable (fun t =>
      ‖dirichletPolynomial chi S c ((sigma : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y := by
  simp_rw [dirichletPolynomial_eq_wave chi S hS]
  exact polynomial_integrable _ _ _ _ _

theorem dirichlet_mean_le (q : ℕ) [NeZero q] {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) (c : ℕ → ℂ) (sigma : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖dirichletPolynomial chi S c ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient ≤
      meanFactor q N y * unitEnergy q S (verticalCoefficient c sigma) -
        (∫ t in -y..y,
          ‖dirichletPolynomial (1 : Character q) S c ((sigma : ℂ) + t * Complex.I)‖ ^ 2) /
          q.totient := by
  have hp : ∀ n ∈ S, 0 < n :=
    fun _ hn => Nat.pos_of_ne_zero (mem_erase.mp (hS hn)).1
  simp_rw [dirichletPolynomial_eq_wave _ S hp]
  exact familyMean_le q hS _ hy

end LiuWang.Proof.NonprincipalDensityMeans
