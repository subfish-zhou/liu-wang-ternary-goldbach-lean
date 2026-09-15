import LiuWang.Proof.WeightedHighZeros.Continuation.Frontier.RightCost

/-! # Paying the residual weight separately on each finite closed height band -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.WeightedHighZeros.Continuation.Frontier

def residualBand (N q : ℕ) [NeZero q] (u y : ℝ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ bandValues chi (1 / 2) u y,
    (analyticOrderNatAt chi.LFunction rho : ℝ) *
      (max ((N : ℝ) ^ (rho.re - 1) - (N : ℝ) ^ (-1 / 50 : ℝ)) 0 / |rho.im|)

def residualShell (N q : ℕ) [NeZero q] (u y : ℝ) : ℝ :=
  max (decay N q y - (N : ℝ) ^ (-1 / 50 : ℝ)) 0 * uniformFamilyBound q y / u

def residualGeometric (N q : ℕ) [NeZero q] (u : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    residualShell N q ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u)

theorem residualBand_mono (N q : ℕ) [NeZero q] (u : ℝ)
    {y z : ℝ} (hyz : y ≤ z) :
    residualBand N q u y ≤ residualBand N q u z := by
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    obtain ⟨hz, ⟨h0, h1, ht⟩, ha, hu⟩ := mem_bandValues.mp hrho
    exact mem_bandValues.mpr ⟨hz, ⟨h0, h1, ht.trans hyz⟩, ha, hu⟩
  · intro rho _ _
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (le_max_right _ _) (abs_nonneg _))

theorem residualBand_split_le (N q : ℕ) [NeZero q] (u v y : ℝ) :
    residualBand N q u y ≤ residualBand N q u v + residualBand N q v y := by
  unfold residualBand
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro chi _
  rw [← Finset.sum_filter_add_sum_filter_not
    (bandValues chi (1 / 2) u y) (fun rho => |rho.im| ≤ v)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hrho
      obtain ⟨hrho, hv⟩ := Finset.mem_filter.mp hrho
      obtain ⟨hz, ⟨h0, h1, _⟩, ha, hu⟩ := mem_bandValues.mp hrho
      exact mem_bandValues.mpr ⟨hz, ⟨h0, h1, hv⟩, ha, hu⟩
    · intro rho _ _
      exact mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (le_max_right _ _) (abs_nonneg _))
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hrho
      obtain ⟨hrho, hv⟩ := Finset.mem_filter.mp hrho
      obtain ⟨hz, ⟨h0, h1, ht⟩, ha, _⟩ := mem_bandValues.mp hrho
      exact mem_bandValues.mpr ⟨hz, ⟨h0, h1, ht⟩, ha, (lt_of_not_ge hv).le⟩
    · intro rho _ _
      exact mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (le_max_right _ _) (abs_nonneg _))

theorem residualBand_le_shell {N q : ℕ} [NeZero q] (hN : 1 ≤ N)
    {u y : ℝ} (hu : 1 ≤ u) (hy : 0 ≤ y) :
    residualBand N q u y ≤ residualShell N q u y := by
  have hu0 : 0 < u := by linarith
  have hf (chi : Character q) (rho : ℂ) (hrho : rho ∈ bandValues chi (1 / 2) u y) :
      max ((N : ℝ) ^ (rho.re - 1) - (N : ℝ) ^ (-1 / 50 : ℝ)) 0 / |rho.im| ≤
        max (decay N q y - (N : ℝ) ^ (-1 / 50 : ℝ)) 0 / u :=
    div_le_div₀ (le_max_right _ _)
      (max_le_max (sub_le_sub_right (band_weight_le_decay hN hu hrho) _) le_rfl)
      hu0 (mem_bandValues.mp hrho).2.2.2
  have hh := family_band_weighted_le_uniform q (alpha := 1 / 2) (by norm_num) hy u
    (fun _ rho => max ((N : ℝ) ^ (rho.re - 1) - (N : ℝ) ^ (-1 / 50 : ℝ)) 0 / |rho.im|)
    (div_nonneg (le_max_right _ _) hu0.le) hf
  exact hh.trans_eq (by unfold residualShell; ring)

theorem residualBand_le_geometric {N q : ℕ} [NeZero q] (hN : 1 ≤ N)
    {u : ℝ} (hu : 1 ≤ u) (k : ℕ) :
    residualBand N q u ((2 : ℝ) ^ (k + 1) * u) ≤ residualGeometric N q u k := by
  have hu0 : 0 < u := by linarith
  induction k with
  | zero =>
    simpa [residualGeometric] using residualBand_le_shell (q := q) hN hu
      (show 0 ≤ 2 * u by positivity)
  | succ k ih =>
    have hlo : 1 ≤ (2 : ℝ) ^ (k + 1) * u :=
      hu.trans (le_mul_of_one_le_left hu0.le (one_le_pow₀ (by norm_num)))
    have hh := residualBand_le_shell (q := q) hN hlo
      (show 0 ≤ (2 : ℝ) ^ (k + 1 + 1) * u by positivity)
    have hs := (residualBand_split_le N q u ((2 : ℝ) ^ (k + 1) * u)
      ((2 : ℝ) ^ (k + 1 + 1) * u)).trans (add_le_add ih hh)
    simpa only [residualGeometric, Finset.sum_range_succ] using hs

theorem source_integral_le_residualGeometric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha) ≤
      residualGeometric N q (omegaCutoff N q) (coverIndex (omegaCutoff N q) (sourceT N) 2) := by
  have hu : 1 ≤ omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have ht := Parameters.sourceT_pos (Parameters.exp_2000_le_of_exp_3100_le hN)
  rw [frontier_integral_eq_remainder (Parameters.nat_pos_of_exp_le hN)]
  exact (residualBand_mono N q (omegaCutoff N q)
    (height_le_cover (by linarith) ht (by norm_num : (1 : ℝ) < 2))).trans
      (residualBand_le_geometric (Parameters.nat_pos_of_exp_le hN) hu _)

theorem residualShell_le_uncapped {N q : ℕ} [NeZero q]
    {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    residualShell N q u y ≤ decay N q y * uniformFamilyBound q y / u := by
  have hb : 0 ≤ uniformFamilyBound q y :=
    (Nat.cast_nonneg (familyCount q 0 y)).trans (familyCount_le_uniformFamilyBound q le_rfl hy)
  have hn : 0 ≤ (N : ℝ) ^ (-1 / 50 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he : max (decay N q y - (N : ℝ) ^ (-1 / 50 : ℝ)) 0 ≤ decay N q y :=
    max_le (by linarith) (Real.exp_pos _).le
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hb) hu

def residualMother (N q : ℕ) [NeZero q] : ℝ :=
  min (uniformRightCost N q)
    (residualGeometric N q (omegaCutoff N q) (coverIndex (omegaCutoff N q) (sourceT N) 2))

theorem source_integral_le_residualMother {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha) ≤
      residualMother N q :=
  le_min (source_integral_le_uniformRightCost hN hq) (source_integral_le_residualGeometric hN hq)

theorem original_residual_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ (1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) + residualMother N q :=
  (original_frontier_uniform_reduction hN hq).trans
    (add_le_add le_rfl (source_integral_le_residualMother hN hq))

theorem original_elementary_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ (1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
      max (Real.exp (-sourceL N / (20 * Real.log (max 10 ((q : ℝ) * sourceL N ^ (15 : ℕ))))) -
        Real.exp (-sourceL N / 50)) 0 *
          (25000 * q * Real.log (sourceL N) ^ (2 : ℕ)) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have he : (N : ℝ) ^ (-1 / 50 : ℝ) = Real.exp (-sourceL N / 50) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
    congr 1
    unfold sourceL
    ring
  have hh := (original_uniform_mother hN hq).trans
    (add_le_add le_rfl (uniformRightCost_le_explicit hN hq))
  simpa only [residualDecay, decay, heightScale, sourceT, he, sourceL] using hh

theorem actual_highPacket_residual_mother {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤ (5 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) + residualMother N q) :=
  (highPacket_le_weighted hN ha heta).trans
    (mul_le_mul_of_nonneg_left (original_residual_mother hN hq) (by positivity))

end LiuWang.Proof.WeightedHighZeros.Continuation.Frontier
