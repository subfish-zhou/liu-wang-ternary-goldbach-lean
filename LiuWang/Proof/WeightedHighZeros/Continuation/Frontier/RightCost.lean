import LiuWang.Proof.WeightedHighZeros.Continuation.Frontier.UniformPayment

/-! # A numerical mother bound for the actual unpaid right integral

The capped base mass is subtracted before any upper bound. This consumes the
admitted uniform reciprocal bound and the frozen ordinary-L R20 region; it
does not assert a high-alpha density or the remaining original coefficient.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation.Frontier

def frontierRemainder (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ highValues N chi,
    (analyticOrderNatAt chi.LFunction rho : ℝ) *
      (max ((N : ℝ) ^ (rho.re - 1) - (N : ℝ) ^ (-1 / 50 : ℝ)) 0 / |rho.im|)

theorem frontierRemainder_nonneg (N q : ℕ) [NeZero q] :
    0 ≤ frontierRemainder N q := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (le_max_right _ _) (abs_nonneg _))))

theorem frontierCap_add_remainder_eq_highSum (N q : ℕ) [NeZero q] :
    frontierCap N q + frontierRemainder N q = highSum N q := by
  unfold frontierCap frontierRemainder
  rw [← Finset.sum_add_distrib]
  change _ = ∑ chi : Character q, ∑ rho ∈ highValues N chi,
    (analyticOrderNatAt chi.LFunction rho : ℝ) * ((N : ℝ) ^ (rho.re - 1) / |rho.im|)
  apply Finset.sum_congr rfl
  intro chi _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases h : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 50 : ℝ)
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    ring

theorem frontier_integral_eq_remainder {N q : ℕ} [NeZero q] (hN : 1 ≤ N) :
    (∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha) =
      frontierRemainder N q := by
  linarith [highSum_eq_frontierCap_add_integral (q := q) hN,
    frontierCap_add_remainder_eq_highSum N q]

def residualDecay (N q : ℕ) : ℝ :=
  max (decay N q (sourceT N) - (N : ℝ) ^ (-1 / 50 : ℝ)) 0

def uniformRightCost (N q : ℕ) [NeZero q] : ℝ :=
  residualDecay N q * uniformReciprocal N q

theorem frontierRemainder_le_reciprocal {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    frontierRemainder N q ≤ residualDecay N q *
      bandSum 1 q (omegaCutoff N q) (sourceT N) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hu : 1 ≤ omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  calc
    _ ≤ ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        (analyticOrderNatAt chi.LFunction rho : ℝ) * (residualDecay N q / |rho.im|) := by
      apply Finset.sum_le_sum
      intro chi _
      apply Finset.sum_le_sum
      intro rho hrho
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      exact max_le_max (sub_le_sub_right (band_weight_le_decay hn hu hrho) _) le_rfl
    _ = _ := by
      simp only [bandSum, highValues, Nat.cast_one, Real.one_rpow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      apply Finset.sum_congr rfl
      intro rho _
      ring

theorem source_integral_le_uniformRightCost {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha) ≤
      uniformRightCost N q := by
  rw [frontier_integral_eq_remainder (Parameters.nat_pos_of_exp_le hN)]
  exact (frontierRemainder_le_reciprocal hN hq).trans
    (mul_le_mul_of_nonneg_left (actual_reciprocal_le_uniform hN) (le_max_right _ _))

theorem uniformRightCost_le_explicit {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    uniformRightCost N q ≤
      residualDecay N q * (25000 * q * Real.log (sourceL N) ^ (2 : ℕ)) :=
  mul_le_mul_of_nonneg_left (uniformReciprocal_paid hN hq) (le_max_right _ _)

theorem original_uniform_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ (1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) + uniformRightCost N q :=
  (original_frontier_uniform_reduction hN hq).trans
    (add_le_add le_rfl (source_integral_le_uniformRightCost hN hq))

theorem actual_primed_uniform_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤
      (1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha := by
  rw [primedHighSum_eq_highSum hN he]
  exact original_frontier_uniform_reduction hN hq

theorem actual_highPacket_uniform_reduction {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤ (5 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha) :=
  (highPacket_le_weighted hN ha heta).trans
    (mul_le_mul_of_nonneg_left (original_frontier_uniform_reduction hN hq) (by positivity))

theorem actual_highPacket_uniform_mother {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤ (5 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) + uniformRightCost N q) :=
  (highPacket_le_weighted hN ha heta).trans
    (mul_le_mul_of_nonneg_left (original_uniform_mother hN hq) (by positivity))

theorem remaining_uniform_coefficient :
    (0.0126 : ℝ) - 1 / 800000 = 10079 / 800000 := by norm_num

end LiuWang.Proof.WeightedHighZeros.Continuation.Frontier
