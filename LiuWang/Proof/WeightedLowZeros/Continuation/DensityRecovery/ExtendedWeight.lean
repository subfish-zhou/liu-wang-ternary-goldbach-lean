import LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery.Consumers

/-!
# The paid ordinary corridor extends from lambda .478 to lambda .27

The rows .36 and .30 pay the intermediate strips. No zero-region or exceptional
source input is used for this truncated sum, throughout the original N range.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery

theorem exp_neg_44 : Real.exp (-44 : ℝ) ≤ 8e-20 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 44
  have he : (1 / (8e-20) : ℝ) ≤ Real.exp 44 := by
    calc
      _ ≤ (2.7182818283 : ℝ)^44 := by norm_num
      _ ≤ Real.exp 1 ^44 := hp
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (8e-20)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem exp_neg_36 : Real.exp (-36 : ℝ) ≤ 2.4e-16 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 36
  have he : (1 / (2.4e-16) : ℝ) ≤ Real.exp 36 := by
    calc
      _ ≤ (2.7182818283 : ℝ)^36 := by norm_num
      _ ≤ Real.exp 1 ^36 := hp
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (2.4e-16)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem exp_neg_33 : Real.exp (-33 : ℝ) ≤ 5e-15 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 33
  have he : (1 / (5e-15) : ℝ) ≤ Real.exp 33 := by
    calc
      _ ≤ (2.7182818283 : ℝ)^33 := by norm_num
      _ ≤ Real.exp 1 ^33 := hp
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (5e-15)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem weight_036_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weight N (cap N 0.36) ≤ 2.5296e-16 / sourceL N := by
  have h := cap_weight_payment hN (c := 0.36) (s := 44) (E := 8e-20) (A := 1.02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exp_neg_44 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem weight_030_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weight N (cap N 0.30) ≤ 7.5888e-13 / sourceL N := by
  have h := cap_weight_payment hN (c := 0.30) (s := 36) (E := 2.4e-16) (A := 1.02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exp_neg_36 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem weight_027_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weight N (cap N 0.27) ≤ 1.581e-11 / sourceL N := by
  have h := cap_weight_payment hN (c := 0.27) (s := 33) (E := 5e-15) (A := 1.02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exp_neg_33 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem cutMass_to_027 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hupper : ∀ chi rho, rho ∈ Z chi → rho.re ≤ cap N 0.27) :
    cutMass N q Z ≤ 7.6e-10 / sourceL N := by
  let A := fun chi => (Z chi).filter (fun rho => rho.re ≤ cap N 0.33)
  let V := fun chi => (Z chi).filter (fun rho => cap N 0.33 < rho.re)
  let B := fun chi => (V chi).filter (fun rho => rho.re ≤ cap N 0.30)
  let C := fun chi => (V chi).filter (fun rho => cap N 0.30 < rho.re)
  have hA : ∀ chi, A chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q) :=
    fun chi => (Finset.filter_subset _ _).trans (hZ chi)
  have hV : ∀ chi, V chi ⊆ Z chi := fun _ => Finset.filter_subset _ _
  have hB : ∀ chi, B chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q) :=
    fun chi => (Finset.filter_subset _ _).trans ((hV chi).trans (hZ chi))
  have hC : ∀ chi, C chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q) :=
    fun chi => (Finset.filter_subset _ _).trans ((hV chi).trans (hZ chi))
  have hfirst := cutMass_le_three_steps (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (bulkCap N) (cap N 0.36) (cap N 0.33)
    (cap_positive hN (by norm_num)) (cap_positive hN (by norm_num)) A hA
    (fun _ _ hr => (Finset.mem_filter.mp hr).2)
  have hsecond := cutMass_le_count (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (cap N 0.33) (cap_positive hN (by norm_num : (0.30 : ℝ) ≤ 0.478)) B hB
    (fun _ _ hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.le)
    (fun _ _ hr => (Finset.mem_filter.mp hr).2)
  have hthird := cutMass_le_count (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (cap N 0.30) (cap_positive hN (by norm_num : (0.27 : ℝ) ≤ 0.478)) C hC
    (fun _ _ hr => (Finset.mem_filter.mp hr).2.le)
    (fun chi rho hr => hupper chi rho (hV chi (Finset.mem_filter.mp hr).1))
  have hc1 : cutCount q A (bulkCap N) ≤ 14000 := by
    simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
      cutCount_low_row .r0478 hN hq A hA (alpha := bulkCap N) le_rfl
  have hc2 : cutCount q A (cap N 0.36) ≤ 20 := by
    simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
      cutCount_low_row .r036 hN hq A hA (alpha := cap N 0.36) le_rfl
  have hc3 : cutCount q B (cap N 0.33) ≤ 13 := by
    simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
      cutCount_low_row .r033 hN hq B hB (alpha := cap N 0.33) le_rfl
  have hc4 : cutCount q C (cap N 0.30) ≤ 9 := by
    simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
      cutCount_low_row .r030 hN hq C hC (alpha := cap N 0.30) (by norm_num [rowLambda])
  have hp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have hw1 := mul_le_mul (weight_036_paid hN) (Nat.cast_le.mpr hc1 : (_ : ℝ) ≤ 14000)
    (Nat.cast_nonneg _) (by positivity)
  have hw2 := mul_le_mul (weight_033_payment hN) (Nat.cast_le.mpr hc2 : (_ : ℝ) ≤ 20)
    (Nat.cast_nonneg _) (by positivity)
  have hw3 := mul_le_mul (weight_030_paid hN) (Nat.cast_le.mpr hc3 : (_ : ℝ) ≤ 13)
    (Nat.cast_nonneg _) (by positivity)
  have hw4 := mul_le_mul (weight_027_paid hN) (Nat.cast_le.mpr hc4 : (_ : ℝ) ≤ 9)
    (Nat.cast_nonneg _) (by positivity)
  have hsplit : cutMass N q Z = cutMass N q A + (cutMass N q B + cutMass N q C) := by
    rw [cutMass_partition N q Z (cap N 0.33)]
    exact congrArg (fun t => cutMass N q A + t) (cutMass_partition N q V (cap N 0.30))
  rw [hsplit]
  apply (add_le_add hfirst (add_le_add hsecond hthird)).trans
  calc
    _ ≤ (6e-10 / sourceL N + (2.5296e-16 / sourceL N) * 14000 +
        (9.486e-15 / sourceL N) * 20) +
        ((7.5888e-13 / sourceL N) * 13 + (1.581e-11 / sourceL N) * 9) :=
      add_le_add (add_le_add (add_le_add (source_bulk_numeric hN hq) hw1) hw2)
        (add_le_add hw3 hw4)
    _ ≤ _ := by
      apply (le_div_iff₀ hp).mpr
      field_simp
      norm_num

theorem actual_bulk_to_027 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    bulkSum N q (omegaCutoff N q) (cap N 0.27) ≤ 7.6e-10 / sourceL N :=
  cutMass_to_027 hN hq
    (fun chi => (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
      (fun rho => rho.re ≤ cap N 0.27))
    (fun _ => Finset.filter_subset _ _) (fun _ _ hr => (Finset.mem_filter.mp hr).2)

theorem actual_bulk_to_027_Jrho {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
        (fun rho => rho.re ≤ cap N 0.27),
          (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
      (N : ℝ) * (7.6e-10 / sourceL N) :=
  (cut_Jrho_le (nat_pos_of_exp_le hN) _ (fun _ => Finset.filter_subset _ _) eta).trans
    (mul_le_mul_of_nonneg_left (actual_bulk_to_027 hN hq) (Nat.cast_nonneg _))

theorem actual_bulk_to_027_packet {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (haq : Nat.Coprime a q)
    (eta : ℝ) :
    ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
        (fun rho => rho.re ≤ cap N 0.27),
          (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (7.6e-10 / sourceL N) :=
  (norm_cutPacket_le (nat_pos_of_exp_le hN) haq eta _
    (fun _ => Finset.filter_subset _ _)).trans
    (mul_le_mul_of_nonneg_left (actual_bulk_to_027 hN hq) (by positivity))

end LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery
