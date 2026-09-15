import LiuWang.Proof.MiddleArcPayment.Oscillation

/-!
# Actual multiplicity counts paying finite height/real-part cells

Closed cells may overlap at height boundaries: the three-cell consumer is an
upper bound, not a disjointness assertion. Real zeros are paid in the first
cell. The unpaid high-real-part packet remains a signed sum of actual zeros.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion
open LiuWang.Proof.OscillatoryBounds

namespace LiuWang.Proof.MiddleArcPayment

def heightCost (N : ℕ) (eta u : ℝ) : ℝ :=
  if 0 < u then min 2
    (min (10 * (0.001 : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt u)
      (if |eta| ≤ u / (10 * Real.pi * (N : ℝ)) then 5 / u
       else 10 * (0.001 : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt u))
  else 2

theorem heightCost_nonneg (N : ℕ) (eta u : ℝ) : 0 ≤ heightCost N eta u := by
  unfold heightCost
  split_ifs <;> positivity

theorem Jrho_le_cell {N : ℕ} (hN : 0 < N) {rho : ℂ} {b u : ℝ}
    (hhalf : 1 / 2 ≤ rho.re) (hb : rho.re ≤ b) (h1 : rho.re ≤ 1)
    (hu : u ≤ |rho.im|) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ (N : ℝ) ^ b * heightCost N eta u := by
  have hr : 0 < rho.re := by linarith
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpow : (N : ℝ) ^ rho.re ≤ (N : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hn hb
  have hw : ‖Jrho N rho eta‖ ≤ (N : ℝ) ^ b * 2 := by
    apply (Jrho_weight hN hr eta).trans
    have hc : (1 - (0.001 : ℝ) ^ rho.re) / rho.re ≤ 2 := by
      apply (div_le_iff₀ hr).mpr
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0.001) rho.re]
    exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0 _)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2)])
  have hs (hu0 : 0 < u) : ‖Jrho N rho eta‖ ≤ (N : ℝ) ^ b *
      (10 * (0.001 : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt u) := by
    have hg : rho.im ≠ 0 := abs_pos.mp (hu0.trans_le hu)
    apply (Jrho_sqrt_ten hN h1 hg eta).trans
    have hc := Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0 : ℝ) < 0.001) (by norm_num : (0.001 : ℝ) ≤ 1)
      (show -(1 / 2 : ℝ) ≤ rho.re - 1 by linarith)
    calc
      _ ≤ 10 * (0.001 : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ b /
          Real.sqrt u := by gcongr
      _ = _ := by ring
  unfold heightCost
  split_ifs with hu0 he
  · have hg : rho.im ≠ 0 := abs_pos.mp (hu0.trans_le hu)
    have hnear : |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) :=
      he.trans (div_le_div_of_nonneg_right hu (by positivity))
    have hf : ‖Jrho N rho eta‖ ≤ (N : ℝ) ^ b * (5 / u) := by
      apply (Jrho_near hN hr.le hg hnear).trans
      calc
        _ ≤ 5 * (N : ℝ) ^ b / u := by gcongr
        _ = _ := by ring
    rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hn0 _),
      mul_min_of_nonneg _ _ (Real.rpow_nonneg hn0 _)]
    exact le_min hw (le_min (hs hu0) hf)
  · rw [min_self, mul_min_of_nonneg _ _ (Real.rpow_nonneg hn0 _)]
    exact le_min hw (hs hu0)
  · exact hw

def cellValues {q : ℕ} [NeZero q] (chi : Character q) (b u v : ℝ) : Finset ℂ :=
  (DirichletZeroCount.zeroValues chi (1 / 2) v).filter
    (fun rho => rho.re ≤ b ∧ u ≤ |rho.im|)

def cellMass {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (eta b u v : ℝ) : ℝ :=
  ∑ rho ∈ cellValues chi b u v,
    (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖

def cellBound {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (eta b u v padding : ℝ) : ℝ :=
  (N : ℝ) ^ b * heightCost N eta u * DirichletZeroCount.sharpenedBound chi v padding

theorem cellMass_le {q N : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) (eta b u : ℝ) {v padding : ℝ}
    (hv : 0 ≤ v) (hp : 0 < padding) :
    cellMass chi N eta b u v ≤ cellBound chi N eta b u v padding := by
  let C := (N : ℝ) ^ b * heightCost N eta u
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (heightCost_nonneg N eta u)
  have hs : (∑ rho ∈ cellValues chi b u v,
      analyticOrderNatAt chi.LFunction rho) ≤ DirichletZeroCount.count chi (1 / 2) v :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc
    _ ≤ ∑ rho ∈ cellValues chi b u v, (analyticOrderNatAt chi.LFunction rho : ℝ) * C := by
      apply Finset.sum_le_sum
      intro rho hrho
      obtain ⟨hz, hb, hu⟩ := Finset.mem_filter.mp hrho
      have hr := DirichletZeroCount.mem_zeroValues.mp hz
      exact mul_le_mul_of_nonneg_left
        (Jrho_le_cell hN hr.2.2 hb hr.2.1.2.1.le hu eta) (Nat.cast_nonneg _)
    _ = C * (∑ rho ∈ cellValues chi b u v, analyticOrderNatAt chi.LFunction rho : ℕ) := by
      simp only [Nat.cast_sum, Finset.mul_sum, mul_comm]
    _ ≤ C * DirichletZeroCount.count chi (1 / 2) v :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hs) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (DirichletZeroCount.count_le_sharpenedBound chi (1 / 2) hv hp) hC

def upperRealSum {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (eta b : ℝ) : ℂ :=
  ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter (fun rho => b < rho.re),
    (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def lowerRealMass {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (eta b : ℝ) : ℝ :=
  ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter (fun rho => rho.re ≤ b),
    (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖

theorem zeroValueSum_sub_upper_le {q : ℕ} [NeZero q]
    (chi : Character q) (N : ℕ) (eta b : ℝ) :
    ‖zeroValueSum chi N (sourceT N) eta - upperRealSum chi N eta b‖ ≤
      lowerRealMass chi N eta b := by
  have he := Finset.sum_filter_add_sum_filter_not
    (CompleteExpansion.zeroValues chi (sourceT N)) (fun rho => b < rho.re)
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta)
  simp only [not_lt] at he
  have hid : zeroValueSum chi N (sourceT N) eta - upperRealSum chi N eta b =
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter (fun rho => rho.re ≤ b),
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
    change _ + _ = zeroValueSum chi N (sourceT N) eta at he
    unfold upperRealSum
    linear_combination -he
  rw [hid]
  simpa only [lowerRealMass, norm_mul, Complex.norm_natCast] using norm_sum_le
    ((CompleteExpansion.zeroValues chi (sourceT N)).filter (fun rho => rho.re ≤ b))
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta)

theorem lowerRealMass_le_cells {q : ℕ} [NeZero q]
    (chi : Character q) (N : ℕ) (eta b U V : ℝ) :
    lowerRealMass chi N eta b ≤
      cellMass chi N eta b 0 U + cellMass chi N eta b U V +
        cellMass chi N eta b V (sourceT N) := by
  let f := fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖
  have hf (rho : ℂ) : 0 ≤ f rho := by dsimp [f]; positivity
  have hunion (s t : Finset ℂ) :
      (∑ rho ∈ s ∪ t, f rho) ≤ (∑ rho ∈ s, f rho) + ∑ rho ∈ t, f rho := by
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun rho _ => hf rho))
  have hsub : (CompleteExpansion.zeroValues chi (sourceT N)).filter (fun rho => rho.re ≤ b) ⊆
      (cellValues chi b 0 U ∪ cellValues chi b U V) ∪ cellValues chi b V (sourceT N) := by
    intro rho hrho
    obtain ⟨hz, hb⟩ := Finset.mem_filter.mp hrho
    have hr := CompleteExpansion.mem_zeroValues.mp hz
    by_cases hU : |rho.im| ≤ U
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨DirichletZeroCount.mem_zeroValues.mpr
        ⟨hr.1, ⟨hr.2.1, hr.2.2.1, hU⟩, hr.2.2.2.2⟩, hb, abs_nonneg _⟩
    · by_cases hV : |rho.im| ≤ V
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨DirichletZeroCount.mem_zeroValues.mpr
          ⟨hr.1, ⟨hr.2.1, hr.2.2.1, hV⟩, hr.2.2.2.2⟩, hb, (lt_of_not_ge hU).le⟩
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨by rwa [← zeroValues_eq_countValues],
          hb, (lt_of_not_ge hV).le⟩
  calc
    _ ≤ ∑ rho ∈ (cellValues chi b 0 U ∪ cellValues chi b U V) ∪
        cellValues chi b V (sourceT N), f rho :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun rho _ _ => hf rho)
    _ ≤ (∑ rho ∈ cellValues chi b 0 U ∪ cellValues chi b U V, f rho) +
        ∑ rho ∈ cellValues chi b V (sourceT N), f rho :=
      hunion _ _
    _ ≤ _ := add_le_add
      (hunion _ _) le_rfl

def characterCountBound {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (eta b U V padding : ℝ) : ℝ :=
  cellBound chi N eta b 0 U padding + cellBound chi N eta b U V padding +
    cellBound chi N eta b V (sourceT N) padding

theorem lowerRealMass_le_count {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (eta b : ℝ)
    {U V padding : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hp : 0 < padding) :
    lowerRealMass chi N eta b ≤ characterCountBound chi N eta b U V padding :=
  (lowerRealMass_le_cells chi N eta b U V).trans
    (add_le_add (add_le_add (cellMass_le (nat_pos_of_exp_le hN) chi eta b 0 hU hp)
      (cellMass_le (nat_pos_of_exp_le hN) chi eta b U hV hp))
      (cellMass_le (nat_pos_of_exp_le hN) chi eta b V (sourceT_pos hN).le hp))

end LiuWang.Proof.MiddleArcPayment
